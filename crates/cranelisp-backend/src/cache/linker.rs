// Minimal linker for loading cached `.o` files.
//
// Loads relocatable object files produced by `cranelift-object`, resolves
// relocations against known symbols (intrinsics, builtins, platform DLLs,
// GOT base addresses), and maps code into executable memory.
//
// Primary target: Mach-O aarch64 (macOS ARM). Also supports ELF aarch64 (Linux ARM).
//
// GOT architecture: per-module GOT tables are heap-allocated during typecheck.
// Object code references them via `__cranelisp_got_{module}` data symbols.
// Decision 23 (Sprint 58 Wave 2 follow-on): the symbol address IS the GOT
// slab base directly — no extra pointer-cell indirection. In `.o` files the
// symbol is defined as `Linkage::Export` data sized `slot_count * 8` with
// function-address relocations at each slot (`define_module_got_data`); in
// JIT mode the symbol is registered via `JITBuilder::symbol()` with
// `GotTable.base_ptr()`. Either way `global_value(__cranelisp_got_{M})`
// resolves to the slab base, after which one load+offset reaches the slot:
//
//   code:
//     ADRP x5, __cranelisp_got_user@GOTPAGE     // system GOT page for the symbol
//     LDR  x5, [x5, #__cranelisp_got_user@GOTPAGEOFF]  // x5 = slab base
//     LDR  x5, [x5, #slot*8]                    // load fn ptr from slot
//     BLR  x5                                   // call
//
// The first ADRP+LDR pair is the system-GOT (literal pool) layer: in object
// mode the system linker materialises it from `ARM64_RELOC_GOT_LOAD_*`
// relocations against an in-process slot allocated by this `Linker`; in JIT
// mode `global_value` lowers identically and resolves through the same
// system-GOT mechanism backed by the JIT's `lookup_symbol`. Same CLIF, same
// machine-code shape, both modes (Decision 23 byte-identical).
//
// See design/backend/module-caching.md §9 for crate placement rationale.

use std::collections::HashMap;

use cranelisp_types::{ErrorLocation, CranelispError, LinkerSymbol, Span};

use crate::error::LinkerError;

/// Mach-O aarch64 relocation types (from mach-o/arm64/reloc.h).
#[allow(dead_code)]
mod macho_arm64 {
    pub const ARM64_RELOC_UNSIGNED: u8 = 0;
    pub const ARM64_RELOC_SUBTRACTOR: u8 = 1;
    pub const ARM64_RELOC_BRANCH26: u8 = 2;
    pub const ARM64_RELOC_PAGE21: u8 = 3;
    pub const ARM64_RELOC_PAGEOFF12: u8 = 4;
    pub const ARM64_RELOC_GOT_LOAD_PAGE21: u8 = 5;
    pub const ARM64_RELOC_GOT_LOAD_PAGEOFF12: u8 = 6;
}

/// ELF aarch64 relocation type constants.
#[allow(dead_code)]
mod elf_aarch64 {
    pub const R_AARCH64_ABS64: u32 = 257;
    pub const R_AARCH64_ADR_PREL_PG_HI21: u32 = 275;
    pub const R_AARCH64_ADD_ABS_LO12_NC: u32 = 277;
    pub const R_AARCH64_CALL26: u32 = 283;
    pub const R_AARCH64_LDST64_ABS_LO12_NC: u32 = 286;
}

/// A minimal linker that loads `.o` files and resolves relocations.
///
/// Symbol addresses are registered externally (from the JIT symbol table)
/// before loading object files. The linker resolves relocations against
/// these known symbols and manages executable memory regions.
pub struct Linker {
    /// Known external symbol addresses (JIT name -> code/data pointer).
    symbols: HashMap<String, usize>,
    /// Defined symbols from loaded .o files (name -> address).
    defined_symbols: HashMap<String, usize>,
    /// Executable memory regions (kept alive for duration of execution).
    code_regions: Vec<ExecutableRegion>,
    /// Data memory regions (kept alive so data symbols remain valid).
    /// Holds constants, string literals, etc. from .o data sections.
    data_regions: Vec<DataRegion>,
    /// Per-symbol GOT slots for `ARM64_RELOC_GOT_LOAD_*` relocations.
    /// Maps a symbol name to the address of an 8-byte slot containing the
    /// symbol's resolved address. The standard system-linker GOT mechanism
    /// for cross-module data references implemented in-process: when
    /// Cranelift emits a GOT_LOAD_PAGE21+PAGEOFF12 pair for an
    /// `Linkage::Import` data symbol (`__cranelisp_got_{M}`), the relocations
    /// resolve against the slot's address — code does ADRP+LDR off the slot
    /// to fetch the symbol value. One slot per unique symbol; reused across
    /// loaded `.o` files. Backed by `got_pool` for lifetime.
    got_slots: HashMap<String, usize>,
    /// Backing storage for `got_slots` — each entry is an mmap'd page-sized
    /// region holding one or more 8-byte GOT entries. Kept alive so the slot
    /// addresses in `got_slots` remain valid for the lifetime of the linker.
    got_pool: Vec<memmap2::MmapMut>,
    /// Number of slots currently used in the most-recently-allocated page in
    /// `got_pool` (each slot is 8 bytes; a 4096-byte page holds 512 slots).
    got_pool_used: usize,
}

/// An mmap'd region that holds executable code.
struct ExecutableRegion {
    #[allow(dead_code)]
    mmap: memmap2::MmapMut,
    #[allow(dead_code)]
    base: usize,
    #[allow(dead_code)]
    size: usize,
}

/// An mmap'd region that holds read-write data (constants, string literals).
struct DataRegion {
    #[allow(dead_code)]
    mmap: memmap2::MmapMut,
    #[allow(dead_code)]
    base: usize,
    #[allow(dead_code)]
    size: usize,
}

impl Linker {
    /// Create a new linker.
    pub fn new() -> Result<Self, CranelispError> {
        Ok(Linker {
            symbols: HashMap::new(),
            defined_symbols: HashMap::new(),
            code_regions: Vec::new(),
            data_regions: Vec::new(),
            got_slots: HashMap::new(),
            got_pool: Vec::new(),
            got_pool_used: 0,
        })
    }

    /// Look up (or allocate) the in-process GOT slot for `target_name` and
    /// return the slot's address. Initialises the slot with the registered
    /// symbol's address on first call. Subsequent calls for the same symbol
    /// return the cached slot address.
    ///
    /// Used by `ARM64_RELOC_GOT_LOAD_*` relocation handling: the relocation
    /// patches code to ADRP+LDR the slot address (not the symbol address);
    /// the LDR pulls the symbol value out of the slot at run time. This is
    /// the standard system-linker GOT mechanism reproduced in-process.
    fn ensure_got_slot(
        &mut self,
        target_name: &str,
        symbol_addr: usize,
    ) -> Result<usize, CranelispError> {
        if let Some(&addr) = self.got_slots.get(target_name) {
            return Ok(addr);
        }

        // Allocate a fresh page for slots if the current page is full or none
        // exists. 4096 bytes / 8 bytes per slot = 512 slots per page; far more
        // than the per-process module count.
        const PAGE_SIZE: usize = 4096;
        const SLOT_SIZE: usize = 8;
        const SLOTS_PER_PAGE: usize = PAGE_SIZE / SLOT_SIZE;

        if self.got_pool.is_empty() || self.got_pool_used >= SLOTS_PER_PAGE {
            let page = memmap2::MmapMut::map_anon(PAGE_SIZE).map_err(|e| {
                CranelispError::CodegenError {
                    message: format!("failed to mmap GOT slot page: {e}"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                }
            })?;
            self.got_pool.push(page);
            self.got_pool_used = 0;
        }

        let page = self
            .got_pool
            .last_mut()
            .expect("got_pool just pushed a page");
        let slot_byte_offset = self.got_pool_used * SLOT_SIZE;
        let slot_addr = page.as_ptr() as usize + slot_byte_offset;
        page[slot_byte_offset..slot_byte_offset + SLOT_SIZE]
            .copy_from_slice(&(symbol_addr as u64).to_le_bytes());
        self.got_pool_used += 1;
        self.got_slots.insert(target_name.to_string(), slot_addr);
        Ok(slot_addr)
    }

    /// Register a known external symbol (intrinsic, builtin, platform function, GOT base).
    pub fn register_symbol(&mut self, name: &str, addr: *const u8) {
        self.symbols.insert(name.to_string(), addr as usize);
    }

    /// Get a defined symbol's address (from a loaded .o file or registered externals).
    ///
    /// Per Decisions 36 + 37 (and `facades/backend.md` §"Linker — the cache-load
    /// retention newtype"): bare-name lookup; returns a typed `LinkerError`
    /// (not a bare `Option`) when the symbol is absent. This makes the
    /// pre-S58 silent-NULL regression net visible at the type level — callers
    /// match on `LinkerError::SymbolNotFound` rather than seeing `None` and
    /// silently substituting a 0 pointer.
    pub fn get_symbol(&self, name: &str) -> Result<*const u8, LinkerError> {
        self.defined_symbols
            .get(name)
            .or_else(|| self.symbols.get(name))
            .map(|&addr| addr as *const u8)
            .ok_or_else(|| LinkerError::SymbolNotFound {
                name: LinkerSymbol::from(name),
            })
    }

    /// Load an object file: parse sections, copy code to executable memory,
    /// resolve relocations, and register defined symbols.
    pub fn load_object(
        &mut self,
        module_name: &str,
        bytes: &[u8],
    ) -> Result<(), CranelispError> {
        use object::{Object, ObjectSection, ObjectSymbol, RelocationFlags, RelocationTarget, SymbolKind};

        let obj = object::File::parse(bytes).map_err(|e| CranelispError::CodegenError {
            message: format!("failed to parse object file: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

        // Find the .text section (Mach-O uses "__text" in "__TEXT" segment)
        let text_section = obj
            .section_by_name("__text")
            .or_else(|| obj.section_by_name(".text"))
            .ok_or_else(|| CranelispError::CodegenError {
                message: "object file has no text section".to_string(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        let text_data = text_section.data().map_err(|e| CranelispError::CodegenError {
            message: format!("failed to read text section: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
        let text_size = text_data.len();

        if text_size == 0 {
            return Ok(());
        }

        // Allocate RW memory, copy code
        let mut mmap =
            memmap2::MmapMut::map_anon(text_size).map_err(|e| CranelispError::CodegenError {
                message: format!("failed to mmap code region: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        mmap[..text_size].copy_from_slice(text_data);
        let base_addr = mmap.as_ptr() as usize;

        // Load data sections (.Ldata* symbols live here — string constants, etc.).
        // These must be loaded before relocation resolution so text-section
        // relocations that reference data symbols can be resolved.
        let mut local_symbols: HashMap<String, usize> = HashMap::new();
        self.load_data_sections(&obj, &mut local_symbols)?;

        // Collect defined text symbols. sym.address() is a virtual address in the
        // object file; subtract the text section's own VA to get an offset into
        // our mmap'd copy.
        let text_section_index = text_section.index();
        let text_section_addr = text_section.address();
        for sym in obj.symbols() {
            if sym.kind() != SymbolKind::Text {
                continue;
            }
            if sym.section_index() != Some(text_section_index) {
                continue;
            }
            if let Ok(name) = sym.name()
                && !name.is_empty()
            {
                // Strip leading underscore (Mach-O prefixes symbols with _)
                let clean_name = name.strip_prefix('_').unwrap_or(name);
                let offset_in_text = (sym.address() - text_section_addr) as usize;
                let addr = base_addr + offset_in_text;
                // Local symbols (.Lfn*) go into a per-object map to avoid
                // cross-module name collisions.
                if clean_name.starts_with(".L") {
                    local_symbols.insert(clean_name.to_string(), addr);
                } else {
                    self.defined_symbols.insert(clean_name.to_string(), addr);

                    // FIXME 0099 — emit a `LinkerWrite` GOT event for each
                    // user-defined text symbol resolved from the cached .o.
                    // The slot index is NOT known to the linker (the
                    // per-module GOT slot lives on the int-side
                    // `SymbolTable.got()`); the consumer correlates by
                    // `(module, symbol)`. The publication is for trace
                    // purposes only; the actual `got().store_slot` call still
                    // happens on the int side after `load_object` returns
                    // (Wave 3b-2 will move/duplicate that write).
                    crate::got_observer::emit(
                        crate::got_observer::GotEventTag::LinkerWrite,
                        &crate::got_observer::GotEvent {
                            module: cranelisp_types::ModuleFullPath::from(module_name),
                            symbol: cranelisp_types::Symbol::from(clean_name),
                            // Slot index is not visible at the linker
                            // boundary; consumer correlates by name. We
                            // publish 0 as a placeholder per facade — the
                            // canonical slot will be added when int's write
                            // site emits.
                            slot: 0,
                            ptr: addr as *const u8,
                            provenance: crate::got_observer::GotProvenance::Linker {
                                linker_addr: (self as *const Linker) as usize,
                            },
                        },
                    );
                }
            }
        }

        // Resolve relocations
        for (offset, reloc) in text_section.relocations() {
            let target_name = match reloc.target() {
                RelocationTarget::Symbol(sym_idx) => {
                    let sym = obj.symbol_by_index(sym_idx).map_err(|e| {
                        CranelispError::CodegenError {
                            message: format!("bad relocation symbol: {e}"),
                            location: ErrorLocation::from_span(Span::SYNTHETIC),
                        }
                    })?;
                    let raw_name = sym.name().map_err(|e| CranelispError::CodegenError {
                        message: format!("bad symbol name: {e}"),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    })?;
                    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
                }
                _ => {
                    return Err(CranelispError::CodegenError {
                        message: "unsupported relocation target".to_string(),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    });
                }
            };

            let raw_target_addr = local_symbols
                .get(&target_name)
                .or_else(|| self.defined_symbols.get(&target_name))
                .or_else(|| self.symbols.get(&target_name))
                .copied()
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("unresolved symbol: {target_name}"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;

            let patch_addr = base_addr + offset as usize;
            let addend = reloc.addend();

            // ARM64_RELOC_GOT_LOAD_* relocations: Cranelift emits these for
            // `Linkage::Import` data symbols accessed via `global_value`
            // (the `__cranelisp_got_{M}` cross-module GOT-base references
            // under Decision 23). The standard system-linker GOT mechanism
            // routes the load through an indirection slot: the code does
            // ADRP+LDR off the SLOT, then LDR off the loaded value. Allocate
            // an in-process slot containing the symbol's address and resolve
            // the relocation against the slot's address (not the symbol's
            // address). See `ensure_got_slot` for slot lifetime management.
            let target_addr = match reloc.flags() {
                RelocationFlags::MachO { r_type, .. }
                    if r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGE21
                        || r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGEOFF12 =>
                {
                    self.ensure_got_slot(&target_name, raw_target_addr)?
                }
                _ => raw_target_addr,
            };

            match reloc.flags() {
                RelocationFlags::MachO {
                    r_type,
                    r_pcrel: _,
                    r_length,
                } => {
                    apply_macho_arm64_reloc(
                        &mut mmap,
                        offset as usize,
                        patch_addr,
                        target_addr,
                        addend,
                        r_type,
                        r_length,
                        &target_name,
                    )?;
                }
                RelocationFlags::Elf { r_type } => {
                    apply_elf_aarch64_reloc(
                        &mut mmap,
                        offset as usize,
                        patch_addr,
                        target_addr,
                        addend,
                        r_type,
                        &target_name,
                    )?;
                }
                flags => {
                    return Err(CranelispError::CodegenError {
                        message: format!(
                            "unsupported relocation flags {flags:?} for '{target_name}'"
                        ),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    });
                }
            }
        }

        // Mark memory executable via mprotect
        #[cfg(unix)]
        {
            let ptr = mmap.as_ptr() as *mut libc::c_void;
            let ret = unsafe {
                libc::mprotect(ptr, text_size, libc::PROT_READ | libc::PROT_EXEC)
            };
            if ret != 0 {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "mprotect failed: {}",
                        std::io::Error::last_os_error()
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
        }

        self.code_regions.push(ExecutableRegion {
            mmap,
            base: base_addr,
            size: text_size,
        });

        Ok(())
    }

    /// Load data sections from an object file and register their symbols.
    ///
    /// Cranelift's ObjectModule emits string constants and other data into
    /// data sections (__data, __const on Mach-O; .data, .rodata on ELF).
    /// These are referenced by `.Ldata*` symbols from the text section.
    /// Without loading these, text relocations to data symbols fail.
    fn load_data_sections(
        &mut self,
        obj: &object::File<'_>,
        local_symbols: &mut HashMap<String, usize>,
    ) -> Result<(), CranelispError> {
        use object::{Object, ObjectSection, ObjectSymbol, SectionKind, SymbolKind};

        // Collect all data sections (read-only and read-write).
        let data_sections: Vec<_> = obj
            .sections()
            .filter(|s| matches!(s.kind(), SectionKind::Data | SectionKind::ReadOnlyData))
            .collect();

        for section in &data_sections {
            let section_data = section.data().map_err(|e| CranelispError::CodegenError {
                message: format!("failed to read data section: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
            if section_data.is_empty() {
                continue;
            }

            // Allocate RW memory for this data section.
            let mut data_mmap = memmap2::MmapMut::map_anon(section_data.len())
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to mmap data region: {e}"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
            data_mmap[..section_data.len()].copy_from_slice(section_data);
            let data_base = data_mmap.as_ptr() as usize;
            let section_addr = section.address();
            let section_index = section.index();

            // Register symbols from this data section.
            //
            // Sprint 60 Wave 2 Step A.3 (single-GOT convergence): data symbols
            // whose name matches `__cranelisp_got_{M}` are NOT registered as
            // defined symbols here. The `.o` file continues to emit them as
            // `Linkage::Export` data (for `--link` mode where the system
            // linker consumes them), but at in-process Cache-Linker load time
            // the authoritative GOT slab base is the one on
            // `SymbolTable[M].got`, pre-registered into `self.symbols` by the
            // session (see `src/worker.rs::load_cached_module_via_linker`
            // around line 3135). If we registered the `.o`'s own data-section
            // address here, `self.defined_symbols` would shadow `self.symbols`
            // (the resolution chain prefers `defined_symbols`), and loaded
            // code would read its function-pointer slots from an un-relocated
            // data region (zero bytes where addresses should be) rather than
            // from the SymbolTable GOT that the fresh-JIT path populates.
            // That dual-GOT breach is the Decision-23 convergence violation
            // reproduced by `tests/sprint60_reduction.rs`. Skipping the
            // registration funnels every GOT_LOAD resolution for
            // `__cranelisp_got_{M}` through `self.symbols` → the one and only
            // GOT slab the REPL can update (Decision 31 Scenario 2).
            //
            // Sprint 60 Wave 2 Step A.3 (defense-in-depth): record the byte
            // range of any `__cranelisp_got_{M}` symbol in this section so we
            // can zero it after registration. Per user ruling 2026-04-21: the
            // `.o`'s data-section GOT is consumed only by `--link` mode's
            // system linker; at in-process load time it's unused. Zeroing
            // ensures any accidental read (e.g., if a future relocation path
            // slipped past our filter) traps loudly on a NULL indirect call
            // rather than work-by-accident against stale pointer values.
            let mut got_ranges_to_zero: Vec<(usize, usize)> = Vec::new();
            for sym in obj.symbols() {
                if sym.kind() != SymbolKind::Data {
                    continue;
                }
                if sym.section_index() != Some(section_index) {
                    continue;
                }
                if let Ok(name) = sym.name()
                    && !name.is_empty()
                {
                    let clean_name = name.strip_prefix('_').unwrap_or(name);
                    let offset = (sym.address() - section_addr) as usize;
                    let addr = data_base + offset;
                    if clean_name.starts_with(".L") {
                        local_symbols.insert(clean_name.to_string(), addr);
                    } else if clean_name.starts_with("__cranelisp_got_") {
                        // Single-GOT convergence: see comment above. The `.o`
                        // exports this data symbol for `--link` compat, but at
                        // in-process load time we rely on `self.symbols` (the
                        // SymbolTable GOT) being the sole resolver.
                        let sym_size = sym.size() as usize;
                        if sym_size > 0 {
                            got_ranges_to_zero.push((offset, sym_size));
                        }
                        continue;
                    } else {
                        self.defined_symbols.insert(clean_name.to_string(), addr);
                    }
                }
            }

            // Defense-in-depth per user ruling 2026-04-21: the .o's
            // data-section GOT is consumed only by `--link` mode's system
            // linker; at in-process load time it's unused. Zeroing ensures
            // any accidental read traps loudly. Must run BEFORE pushing the
            // DataRegion so the mmap is still accessible through `data_mmap`.
            for (offset, size) in &got_ranges_to_zero {
                // SAFETY: `data_mmap` is a freshly mmap'd, still-mutable
                // MmapMut we own exclusively; `offset + size` is within
                // `section_data.len()` because it came from the section's
                // own symbol table.
                unsafe {
                    std::ptr::write_bytes(
                        data_mmap.as_mut_ptr().add(*offset),
                        0,
                        *size,
                    );
                }
                debug_assert!(
                    data_mmap[*offset..*offset + *size].iter().all(|&b| b == 0),
                    "defense-in-depth zeroing of __cranelisp_got_ bytes \
                     at offset {offset} (size {size}) failed"
                );
            }

            self.data_regions.push(DataRegion {
                mmap: data_mmap,
                base: data_base,
                size: section_data.len(),
            });
        }

        Ok(())
    }
}

/// Apply a Mach-O aarch64 relocation.
#[allow(clippy::too_many_arguments)]
fn apply_macho_arm64_reloc(
    mmap: &mut memmap2::MmapMut,
    offset: usize,
    patch_addr: usize,
    target_addr: usize,
    addend: i64,
    r_type: u8,
    r_length: u8,
    target_name: &str,
) -> Result<(), CranelispError> {
    match r_type {
        // ARM64_RELOC_BRANCH26: B/BL branch (26-bit offset, 4-byte aligned)
        //
        // Range limit: BL has ±128MB range on aarch64 (26-bit signed offset * 4).
        // If loaded .o code is far from runtime intrinsics or platform DLL functions,
        // this relocation will fail. The diagnostic below catches this with a clear
        // message.
        //
        // Fallback plan (if this ever triggers): Replace direct BL calls to external
        // functions with ADRP+LDR+BLR via literal pool entries (Export data), the
        // same pattern used for GOT base addresses. This requires changes to
        // compile_all_functions to emit indirect calls for intrinsics instead of
        // declaring them as Linkage::Import.
        macho_arm64::ARM64_RELOC_BRANCH26 => {
            let rel_offset = (target_addr as i64 + addend - patch_addr as i64) >> 2;

            // Diagnostic assertion: check ±128MB range (2^25 instructions = 2^27 bytes)
            const BL_MAX_RANGE: i64 = 1 << 25; // ±128MB in instruction units
            if !(-BL_MAX_RANGE..BL_MAX_RANGE).contains(&rel_offset) {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "BRANCH26 (BL) target '{target_name}' out of ±128MB range: \
                         offset={rel_offset} instructions ({} bytes). \
                         This means loaded .o code is too far from the target function. \
                         Fix: emit ADRP+LDR+BLR (indirect call via literal pool entry) \
                         instead of BL for external function calls.",
                        rel_offset * 4
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
            let existing =
                u32::from_le_bytes(mmap[offset..offset + 4].try_into().unwrap());
            let patched =
                (existing & 0xFC00_0000) | ((rel_offset as u32) & 0x03FF_FFFF);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        // ARM64_RELOC_PAGE21 / ARM64_RELOC_GOT_LOAD_PAGE21: ADRP (21-bit page offset)
        macho_arm64::ARM64_RELOC_PAGE21 | macho_arm64::ARM64_RELOC_GOT_LOAD_PAGE21 => {
            let target_page = ((target_addr as i64 + addend) >> 12) << 12;
            let patch_page = (patch_addr as i64 >> 12) << 12;
            let page_offset = ((target_page - patch_page) >> 12) as i32;

            let existing =
                u32::from_le_bytes(mmap[offset..offset + 4].try_into().unwrap());
            let immlo = ((page_offset as u32) & 0x3) << 29;
            let immhi = (((page_offset as u32) >> 2) & 0x7FFFF) << 5;
            let patched = (existing & 0x9F00_001F) | immhi | immlo;
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        // ARM64_RELOC_PAGEOFF12 / ARM64_RELOC_GOT_LOAD_PAGEOFF12: page offset (12-bit)
        macho_arm64::ARM64_RELOC_PAGEOFF12
        | macho_arm64::ARM64_RELOC_GOT_LOAD_PAGEOFF12 => {
            let page_off = ((target_addr as i64 + addend) & 0xFFF) as u32;
            let existing =
                u32::from_le_bytes(mmap[offset..offset + 4].try_into().unwrap());
            // Detect instruction type to determine scaling
            let opc = (existing >> 22) & 0x3FF;
            let shift = if opc & 0x3E0 == 0x3E0 {
                // LDR/STR 64-bit: scale by 8
                3
            } else if opc & 0x3E0 == 0x2E0 {
                // LDR/STR 32-bit: scale by 4
                2
            } else {
                // ADD: no scaling
                0
            };
            let imm12 = (page_off >> shift) & 0xFFF;
            let patched = (existing & 0xFFC0_03FF) | (imm12 << 10);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        // ARM64_RELOC_UNSIGNED: absolute pointer
        macho_arm64::ARM64_RELOC_UNSIGNED if r_length == 3 => {
            let abs_val = (target_addr as i64 + addend) as u64;
            mmap[offset..offset + 8].copy_from_slice(&abs_val.to_le_bytes());
        }
        _ => {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "unsupported Mach-O ARM64 relocation type {r_type} for '{target_name}'"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
    }
    Ok(())
}

/// Apply an ELF aarch64 relocation (for Linux targets).
fn apply_elf_aarch64_reloc(
    mmap: &mut memmap2::MmapMut,
    offset: usize,
    patch_addr: usize,
    target_addr: usize,
    addend: i64,
    r_type: u32,
    target_name: &str,
) -> Result<(), CranelispError> {
    match r_type {
        // R_AARCH64_CALL26: same ±128MB range limit as Mach-O BRANCH26.
        // See apply_macho_arm64_reloc for the diagnostic rationale.
        elf_aarch64::R_AARCH64_CALL26 => {
            let rel_offset = (target_addr as i64 + addend - patch_addr as i64) >> 2;
            const BL_MAX_RANGE: i64 = 1 << 25;
            if !(-BL_MAX_RANGE..BL_MAX_RANGE).contains(&rel_offset) {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "CALL26 (BL) target '{target_name}' out of ±128MB range: \
                         offset={rel_offset} instructions ({} bytes). \
                         Fix: emit ADRP+LDR+BLR for external function calls.",
                        rel_offset * 4
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
            let existing =
                u32::from_le_bytes(mmap[offset..offset + 4].try_into().unwrap());
            let patched =
                (existing & 0xFC00_0000) | ((rel_offset as u32) & 0x03FF_FFFF);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        elf_aarch64::R_AARCH64_ADR_PREL_PG_HI21 => {
            let target_page = ((target_addr as i64 + addend) >> 12) << 12;
            let patch_page = (patch_addr as i64 >> 12) << 12;
            let page_offset = ((target_page - patch_page) >> 12) as i32;

            let existing =
                u32::from_le_bytes(mmap[offset..offset + 4].try_into().unwrap());
            let immlo = ((page_offset as u32) & 0x3) << 29;
            let immhi = (((page_offset as u32) >> 2) & 0x7FFFF) << 5;
            let patched = (existing & 0x9F00_001F) | immhi | immlo;
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        elf_aarch64::R_AARCH64_ADD_ABS_LO12_NC => {
            let page_off = ((target_addr as i64 + addend) & 0xFFF) as u32;
            let existing =
                u32::from_le_bytes(mmap[offset..offset + 4].try_into().unwrap());
            let patched = (existing & 0xFFC0_03FF) | ((page_off & 0xFFF) << 10);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        elf_aarch64::R_AARCH64_LDST64_ABS_LO12_NC => {
            let page_off = ((target_addr as i64 + addend) & 0xFFF) as u32;
            let existing =
                u32::from_le_bytes(mmap[offset..offset + 4].try_into().unwrap());
            let imm12 = (page_off >> 3) & 0xFFF;
            let patched = (existing & 0xFFC0_03FF) | (imm12 << 10);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        elf_aarch64::R_AARCH64_ABS64 => {
            let abs_val = (target_addr as i64 + addend) as u64;
            mmap[offset..offset + 8].copy_from_slice(&abs_val.to_le_bytes());
        }
        _ => {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "unsupported ELF aarch64 relocation type {r_type} for '{target_name}'"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/backend/module-caching.md §9 — linker symbol registration and lookup
    #[test]
    fn test_linker_register_and_lookup() {
        let mut linker = Linker::new().unwrap();
        let addr = 0x1234usize as *const u8;
        linker.register_symbol("runtime/alloc", addr);
        assert_eq!(linker.get_symbol("runtime/alloc").ok(), Some(addr));
    }

    // spec: design/backend/module-caching.md §9 — linker returns LinkerError::SymbolNotFound
    //       for unknown symbols (Decision 37; typed-error contract).
    #[test]
    fn test_linker_unknown_symbol() {
        let linker = Linker::new().unwrap();
        let result = linker.get_symbol("nonexistent");
        assert!(matches!(result, Err(LinkerError::SymbolNotFound { .. })));
    }

    // spec: design/backend/module-caching.md §9 — linker creation succeeds
    #[test]
    fn test_linker_new() {
        let linker = Linker::new().unwrap();
        assert!(linker.symbols.is_empty());
    }

    // spec: design/arch/CLAUDE.md Decision 23 — Sprint 58 Wave 2 regression
    // guard. Cranelift emits `ARM64_RELOC_GOT_LOAD_PAGE21` /
    // `ARM64_RELOC_GOT_LOAD_PAGEOFF12` relocations when CLIF references an
    // `Linkage::Import` data symbol (such as `__cranelisp_got_{M}` for cross-
    // module GOT-base references) via `global_value`. The cache `Linker` MUST
    // resolve these by allocating an in-process slot containing the
    // registered symbol's address and patching the relocations to point at
    // the slot (not the symbol). This test synthesizes an .o with such a
    // reference, loads it via the linker, and asserts the slot contains the
    // registered symbol's address.
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn linker_resolves_arm64_got_load_relocations() {
        use cranelift::codegen::Context;
        use cranelift::codegen::ir::{Function, UserFuncName, types};
        use cranelift::prelude::{
            AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder, Signature,
        };
        use cranelift_module::{Linkage, Module};
        use cranelift_object::{ObjectBuilder, ObjectModule};

        // Build an aarch64 PIC ISA — same as the cache build path.
        let isa = crate::cache::object::build_isa(true).unwrap();
        let call_conv = isa.default_call_conv();
        let builder = ObjectBuilder::new(
            isa,
            "got_load_reloc_test",
            cranelift_module::default_libcall_names(),
        )
        .unwrap();
        let mut module = ObjectModule::new(builder);

        // Declare an Import data symbol — the canonical case that triggers
        // GOT_LOAD relocations on aarch64 macOS.
        let import_data = module
            .declare_data("__cranelisp_got_imported", Linkage::Import, false, false)
            .unwrap();

        // Declare a function `get_got_base` that returns the address of the
        // import data symbol (mirroring how compile_to_module's
        // `emit_got_indirect_call_via_data_id` emits the slab base — the
        // symbol address IS the slab base, no extra pointer-cell deref).
        let mut sig = Signature::new(call_conv);
        sig.returns.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function("get_got_base", Linkage::Export, &sig)
            .unwrap();

        let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig.clone());
        let mut fbc = FunctionBuilderContext::new();
        {
            let import_gv = module.declare_data_in_func(import_data, &mut func);
            let mut fb = FunctionBuilder::new(&mut func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let addr = fb.ins().symbol_value(types::I64, import_gv);
            fb.ins().return_(&[addr]);
            fb.finalize();
        }

        let mut ctx = Context::for_function(func);
        module.define_function(func_id, &mut ctx).unwrap();

        let product = module.finish();
        let bytes = product.emit().unwrap();

        // Sanity: the synthesised .o must contain GOT_LOAD relocations against
        // our import symbol — otherwise the test would not exercise the new
        // code path.
        {
            use ::object::{
                Object, ObjectSection, ObjectSymbol, RelocationFlags, RelocationTarget,
            };
            let parsed = ::object::File::parse(&*bytes).unwrap();
            let text = parsed
                .section_by_name("__text")
                .or_else(|| parsed.section_by_name(".text"))
                .expect("text section must exist");
            let mut got_load_count = 0usize;
            for (_off, reloc) in text.relocations() {
                if let RelocationTarget::Symbol(sym_idx) = reloc.target() {
                    let sym = parsed.symbol_by_index(sym_idx).unwrap();
                    let nm = sym.name().unwrap_or("");
                    let clean = nm.strip_prefix('_').unwrap_or(nm);
                    if clean == "__cranelisp_got_imported"
                        && let RelocationFlags::MachO { r_type, .. } = reloc.flags()
                        && (r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGE21
                            || r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGEOFF12)
                    {
                        got_load_count += 1;
                    }
                }
            }
            assert!(
                got_load_count >= 2,
                "synthesised .o must emit at least one GOT_LOAD_PAGE21 + \
                 GOT_LOAD_PAGEOFF12 pair against the Import symbol so this \
                 test exercises the new code path; got {got_load_count}"
            );
        }

        // Use the address of a stable heap allocation as the registered
        // symbol value. The slot will be initialised with this address.
        let stable: Box<u64> = Box::new(0xDEAD_BEEF_F00D_CAFEu64);
        let stable_ptr: *const u64 = &*stable;
        let mut linker = Linker::new().unwrap();
        linker.register_symbol("__cranelisp_got_imported", stable_ptr as *const u8);

        // Load the synthesised .o — this MUST NOT error on the GOT_LOAD relocs.
        linker
            .load_object("got_load_reloc_test", &bytes)
            .expect("linker must accept GOT_LOAD relocations and resolve them via in-process slots");

        // Verify the linker allocated a GOT slot for the symbol and the slot
        // contains the registered address (the slot is the indirection that
        // the patched ADRP+LDR will load through at runtime).
        let slot_addr = *linker
            .got_slots
            .get("__cranelisp_got_imported")
            .expect("linker must allocate a GOT slot for the GOT_LOAD-referenced symbol");
        let stored = unsafe { *(slot_addr as *const u64) };
        assert_eq!(
            stored, stable_ptr as u64,
            "GOT slot must hold the registered symbol address; got {:#x}",
            stored
        );

        // Keep `stable` alive until after the assertion (drop runs at end of fn).
        drop(stable);
    }

    // spec: design/backend/cache-repl-loads-triage.md — Sprint 59 Wave 1 C-ii
    // regression guard. Cranelift emits `ARM64_RELOC_GOT_LOAD_*` relocations
    // not only against `Linkage::Import` data symbols but also against local
    // `.L*` data labels it synthesises for string-literal constants
    // (e.g. panic messages in trait-method dispatchers). Those local symbols
    // live in the per-object `local_symbols` map — not in `self.defined_symbols`
    // or `self.symbols`. `ensure_got_slot` must accept the pre-resolved address
    // from its caller rather than re-looking-up the symbol by name, so that
    // GOT-slot allocation succeeds for local data labels too. Extends the
    // Decision-23 regression-guard coverage to `.L*` locals.
    #[test]
    fn ensure_got_slot_accepts_preresolved_local_symbol_address() {
        let mut linker = Linker::new().unwrap();
        // Simulate a `.L`-local data symbol's address resolved by the outer
        // relocation loop from a per-object `local_symbols` map. The symbol
        // is NOT registered via `register_symbol` and is NOT in
        // `defined_symbols` — exactly the condition that caused the
        // pre-fix `undefined symbol` error.
        let stable: Box<u64> = Box::new(0xFEED_FACE_DEAD_BEEFu64);
        let stable_ptr: *const u64 = &*stable;
        let pre_resolved_addr = stable_ptr as usize;

        assert!(
            !linker.defined_symbols.contains_key(".Ldata0"),
            "precondition: .Ldata0 must not be pre-registered (that's the whole bug shape)"
        );
        assert!(
            !linker.symbols.contains_key(".Ldata0"),
            "precondition: .Ldata0 must not be in the external-symbol table either"
        );

        let slot_addr = linker
            .ensure_got_slot(".Ldata0", pre_resolved_addr)
            .expect("ensure_got_slot must accept a pre-resolved local symbol address");
        let stored = unsafe { *(slot_addr as *const u64) };
        assert_eq!(
            stored, pre_resolved_addr as u64,
            "GOT slot must hold the caller-supplied address"
        );

        // Second call for the same symbol returns the same slot (idempotent).
        let slot_addr2 = linker
            .ensure_got_slot(".Ldata0", pre_resolved_addr)
            .expect("second call must return cached slot");
        assert_eq!(slot_addr, slot_addr2, "repeat calls return the same slot");

        drop(stable);
    }

    // spec: design/arch/CLAUDE.md Decision 23 + Sprint 60 Wave 2 Step A.3
    // (single-GOT convergence). When a cached `.o` file is loaded,
    // `load_data_sections` must NOT register the `.o`'s own
    // `__cranelisp_got_{M}` export into `self.defined_symbols` — the
    // authoritative GOT slab base is the in-process `SymbolTable[M].got`
    // registered externally via `register_symbol`. Allowing the `.o`'s own
    // data address to shadow the externally-registered symbol is the
    // dual-GOT breach reproduced by `tests/sprint60_reduction.rs`. This
    // unit test synthesises an `.o` whose data section exports
    // `__cranelisp_got_imported`, loads it alongside an external
    // registration, and asserts that the GOT slot is initialised to the
    // externally-registered address — not to the `.o`'s own data section.
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn loaded_object_does_not_shadow_externally_registered_got_symbol() {
        use cranelift::codegen::Context;
        use cranelift::codegen::ir::{Function, UserFuncName, types};
        use cranelift::prelude::{
            AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder, Signature,
        };
        use cranelift_module::{DataDescription, Linkage, Module};
        use cranelift_object::{ObjectBuilder, ObjectModule};

        let isa = crate::cache::object::build_isa(true).unwrap();
        let call_conv = isa.default_call_conv();
        let builder = ObjectBuilder::new(
            isa,
            "got_convergence_test",
            cranelift_module::default_libcall_names(),
        )
        .unwrap();
        let mut module = ObjectModule::new(builder);

        // Define the GOT data symbol as Export (the shape a compiled
        // `.o` file has for its own-module GOT — the `--link` path needs
        // this symbol exported so the system linker can resolve it).
        let got_data = module
            .declare_data("__cranelisp_got_imported", Linkage::Export, false, false)
            .unwrap();
        let mut desc = DataDescription::new();
        // 16 bytes = 2 slots, zero-filled (no relocations) — simulates
        // the worst case where the `.o`'s own data section is never
        // relocated (if we trust it we segfault on indirect call).
        desc.define(vec![0u8; 16].into_boxed_slice());
        module.define_data(got_data, &desc).unwrap();

        // A tiny function so the `.o` is non-empty.
        let mut sig = Signature::new(call_conv);
        sig.returns.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function("unused", Linkage::Export, &sig)
            .unwrap();
        let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig.clone());
        let mut fbc = FunctionBuilderContext::new();
        {
            let mut fb = FunctionBuilder::new(&mut func, &mut fbc);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.seal_block(entry);
            let zero = fb.ins().iconst(types::I64, 0);
            fb.ins().return_(&[zero]);
            fb.finalize();
        }
        let mut ctx = Context::for_function(func);
        module.define_function(func_id, &mut ctx).unwrap();

        let bytes = module.finish().emit().unwrap();

        // Register the authoritative GOT base externally FIRST, just as
        // `src/worker.rs::load_cached_module_via_linker` does.
        let authoritative: Box<[u64; 2]> = Box::new([0xAAAA_AAAA_AAAA_AAAA, 0xBBBB_BBBB_BBBB_BBBB]);
        let authoritative_ptr = authoritative.as_ptr() as *const u8;
        let mut linker = Linker::new().unwrap();
        linker.register_symbol("__cranelisp_got_imported", authoritative_ptr);

        linker
            .load_object("got_convergence_test", &bytes)
            .expect("linker must accept the .o");

        // Convergence invariant: the loaded `.o`'s own
        // `__cranelisp_got_imported` data-section address must NOT
        // shadow the externally-registered authoritative GOT base.
        assert!(
            !linker
                .defined_symbols
                .contains_key("__cranelisp_got_imported"),
            "loading a .o must NOT insert __cranelisp_got_* into \
             defined_symbols; the externally-registered SymbolTable.got \
             base is the sole authoritative resolver (single-GOT)"
        );
        // `get_symbol` must return the externally-registered address.
        assert_eq!(
            linker.get_symbol("__cranelisp_got_imported").ok(),
            Some(authoritative_ptr),
            "get_symbol for __cranelisp_got_* must return the \
             externally-registered SymbolTable GOT base"
        );

        drop(authoritative);
    }
}
