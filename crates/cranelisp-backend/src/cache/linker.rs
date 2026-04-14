// Minimal linker for loading cached `.o` files.
//
// Loads relocatable object files produced by `cranelift-object`, resolves
// relocations against known symbols (intrinsics, builtins, platform DLLs,
// GOT base addresses), and maps code into executable memory.
//
// Primary target: Mach-O aarch64 (macOS ARM). Also supports ELF aarch64 (Linux ARM).
//
// GOT architecture: per-module GOT tables are heap-allocated during typecheck.
// Object code references them via `__cranelisp_got_{module}` data symbols,
// each declared as Export data (8-byte literal pool entry) in the .o file.
// The linker patches these entries with actual GotTable heap addresses at
// load time. Code uses ADRP+LDR from the co-located data section to load
// the GOT base, then indexes into the GOT for function dispatch:
//
//   .o data section (patched by linker):
//     __cranelisp_got_user:    0x12345000  // heap address of user's GotTable
//     __cranelisp_got_prelude: 0x12346000  // heap address of prelude's GotTable
//
//   code:
//     ADRP x5, __cranelisp_got_user  // page of data entry (always reachable)
//     LDR  x5, [x5, #off]            // load GOT base from data section
//     LDR  x5, [x5, #slot*8]         // load fn ptr from GOT
//     BLR  x5                         // call
//
// See design/backend/module-caching.md §9 for crate placement rationale.

use std::collections::HashMap;

use cranelisp_types::{CranelispError, Span};

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
        })
    }

    /// Register a known external symbol (intrinsic, builtin, platform function, GOT base).
    pub fn register_symbol(&mut self, name: &str, addr: *const u8) {
        self.symbols.insert(name.to_string(), addr as usize);
    }

    /// Get a defined symbol's address (from a loaded .o file or registered externals).
    pub fn get_symbol(&self, name: &str) -> Option<*const u8> {
        self.defined_symbols
            .get(name)
            .or_else(|| self.symbols.get(name))
            .map(|&addr| addr as *const u8)
    }

    /// Load an object file: parse sections, copy code to executable memory,
    /// resolve relocations, and register defined symbols.
    pub fn load_object(
        &mut self,
        _module_name: &str,
        bytes: &[u8],
    ) -> Result<(), CranelispError> {
        use object::{Object, ObjectSection, ObjectSymbol, RelocationFlags, RelocationTarget, SymbolKind};

        let obj = object::File::parse(bytes).map_err(|e| CranelispError::CodegenError {
            message: format!("failed to parse object file: {e}"),
            span: Span::SYNTHETIC,
        })?;

        // Find the .text section (Mach-O uses "__text" in "__TEXT" segment)
        let text_section = obj
            .section_by_name("__text")
            .or_else(|| obj.section_by_name(".text"))
            .ok_or_else(|| CranelispError::CodegenError {
                message: "object file has no text section".to_string(),
                span: Span::SYNTHETIC,
            })?;
        let text_data = text_section.data().map_err(|e| CranelispError::CodegenError {
            message: format!("failed to read text section: {e}"),
            span: Span::SYNTHETIC,
        })?;
        let text_size = text_data.len();

        if text_size == 0 {
            return Ok(());
        }

        // Allocate RW memory, copy code
        let mut mmap =
            memmap2::MmapMut::map_anon(text_size).map_err(|e| CranelispError::CodegenError {
                message: format!("failed to mmap code region: {e}"),
                span: Span::SYNTHETIC,
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
                            span: Span::SYNTHETIC,
                        }
                    })?;
                    let raw_name = sym.name().map_err(|e| CranelispError::CodegenError {
                        message: format!("bad symbol name: {e}"),
                        span: Span::SYNTHETIC,
                    })?;
                    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
                }
                _ => {
                    return Err(CranelispError::CodegenError {
                        message: "unsupported relocation target".to_string(),
                        span: Span::SYNTHETIC,
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
                    span: Span::SYNTHETIC,
                })?;

            let patch_addr = base_addr + offset as usize;
            let addend = reloc.addend();

            // GOT-load relocations should not occur: all __cranelisp_got_*
            // symbols are Export data in the .o (literal pool entries), so
            // Cranelift emits PAGE21+PAGEOFF12, not GOT_LOAD.
            if let RelocationFlags::MachO { r_type, .. } = reloc.flags()
                && (r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGE21
                    || r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGEOFF12)
            {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "unexpected GOT-load relocation for '{}' — \
                         all GOT data symbols should be Export (literal pool entries)",
                        target_name,
                    ),
                    span: Span::SYNTHETIC,
                });
            }
            let target_addr = raw_target_addr;

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
                        span: Span::SYNTHETIC,
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
                    span: Span::SYNTHETIC,
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
                span: Span::SYNTHETIC,
            })?;
            if section_data.is_empty() {
                continue;
            }

            // Allocate RW memory for this data section.
            let mut data_mmap = memmap2::MmapMut::map_anon(section_data.len())
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to mmap data region: {e}"),
                    span: Span::SYNTHETIC,
                })?;
            data_mmap[..section_data.len()].copy_from_slice(section_data);
            let data_base = data_mmap.as_ptr() as usize;
            let section_addr = section.address();
            let section_index = section.index();

            // Register symbols from this data section.
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
                    } else {
                        self.defined_symbols.insert(clean_name.to_string(), addr);
                    }
                }
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
                    span: Span::SYNTHETIC,
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
                span: Span::SYNTHETIC,
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
                    span: Span::SYNTHETIC,
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
                span: Span::SYNTHETIC,
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
        assert_eq!(linker.get_symbol("runtime/alloc"), Some(addr));
    }

    // spec: design/backend/module-caching.md §9 — linker returns None for unknown symbol
    #[test]
    fn test_linker_unknown_symbol() {
        let linker = Linker::new().unwrap();
        assert_eq!(linker.get_symbol("nonexistent"), None);
    }

    // spec: design/backend/module-caching.md §9 — linker creation succeeds
    #[test]
    fn test_linker_new() {
        let linker = Linker::new().unwrap();
        assert!(linker.symbols.is_empty());
    }
}
