//! Minimal linker for loading cached `.o` files.
//!
//! Loads relocatable object files produced by `cranelift-object`, resolves
//! relocations against known symbols (intrinsics, builtins, platform DLLs,
//! GOT base addresses), and maps code into executable memory.

use std::collections::HashMap;

use memmap2::MmapMut;
use object::read::Object;
use object::{ObjectSection, ObjectSymbol, RelocationFlags, RelocationTarget, SymbolKind};

use crate::error::CranelispError;

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

/// A minimal linker that loads `.o` files and resolves relocations.
pub struct Linker {
    /// Known symbol addresses (JIT name -> code/data pointer).
    symbols: HashMap<String, usize>,
    /// Executable memory regions (kept alive for duration of execution).
    #[allow(dead_code)]
    code_regions: Vec<ExecutableRegion>,
    /// Defined symbols from loaded .o files (name -> address).
    defined_symbols: HashMap<String, usize>,
    /// Linker-internal GOT: mmap-backed slots for GOT-load relocations.
    /// Each slot holds a target address; the ADRP+LDR pair loads from here.
    /// Maps symbol name -> index into the `got_mmap`.
    got_slots: HashMap<String, usize>,
    /// mmap-backed GOT table. Must be in the same address region as code mmaps
    /// so that ADRP (±4GB range) can reach it.
    got_mmap: Option<MmapMut>,
    /// Base address of got_mmap.
    got_mmap_base: usize,
    /// Number of GOT entries currently allocated.
    got_count: usize,
}

/// An mmap'd region that holds executable code.
struct ExecutableRegion {
    #[allow(dead_code)]
    mmap: MmapMut,
    #[allow(dead_code)]
    base: usize,
    #[allow(dead_code)]
    size: usize,
}

/// Maximum number of GOT entries in the linker-internal GOT (one 4KB page = 512 entries).
const LINKER_GOT_MAX_ENTRIES: usize = 512;

impl Default for Linker {
    fn default() -> Self {
        Self::new()
    }
}

impl Linker {
    pub fn new() -> Self {
        // Allocate an mmap page for the linker-internal GOT table.
        // This must be allocated via mmap (not the heap) so it ends up in the same
        // address region as code mmaps, within ADRP's ±4GB range.
        let got_size = LINKER_GOT_MAX_ENTRIES * 8;
        let got_mmap = MmapMut::map_anon(got_size).expect("failed to mmap linker GOT");
        let got_mmap_base = got_mmap.as_ptr() as usize;

        Linker {
            symbols: HashMap::new(),
            code_regions: Vec::new(),
            defined_symbols: HashMap::new(),
            got_slots: HashMap::new(),
            got_mmap: Some(got_mmap),
            got_mmap_base,
            got_count: 0,
        }
    }

    /// Get or create a GOT slot for a symbol. Returns the address of the GOT entry
    /// (an 8-byte cell containing the target address). Used for GOT-load relocations
    /// where the code uses ADRP+LDR to load a pointer from this cell.
    fn get_or_create_got_slot(&mut self, name: &str, target_addr: usize) -> usize {
        if let Some(&idx) = self.got_slots.get(name) {
            // Update the entry (address might have changed)
            let slot_addr = self.got_mmap_base + idx * 8;
            let mmap = self.got_mmap.as_mut().unwrap();
            mmap[idx * 8..idx * 8 + 8].copy_from_slice(&(target_addr as u64).to_le_bytes());
            return slot_addr;
        }
        assert!(
            self.got_count < LINKER_GOT_MAX_ENTRIES,
            "linker GOT overflow: too many GOT-load symbols"
        );
        let idx = self.got_count;
        self.got_count += 1;
        let slot_addr = self.got_mmap_base + idx * 8;
        let mmap = self.got_mmap.as_mut().unwrap();
        mmap[idx * 8..idx * 8 + 8].copy_from_slice(&(target_addr as u64).to_le_bytes());
        self.got_slots.insert(name.to_string(), idx);
        slot_addr
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
        let obj = object::File::parse(bytes).map_err(|e| CranelispError::CodegenError {
            message: format!("failed to parse object file: {}", e),
            span: (0, 0),
        })?;

        // Find the .text section (Mach-O uses "__text" in "__TEXT" segment)
        let text_section = obj
            .section_by_name("__text")
            .or_else(|| obj.section_by_name(".text"))
            .ok_or_else(|| CranelispError::CodegenError {
                message: "object file has no text section".to_string(),
                span: (0, 0),
            })?;
        let text_data = text_section.data().map_err(|e| CranelispError::CodegenError {
            message: format!("failed to read text section: {}", e),
            span: (0, 0),
        })?;
        let text_size = text_data.len();

        if text_size == 0 {
            return Ok(());
        }

        // Allocate RW memory, copy code
        let mut mmap =
            MmapMut::map_anon(text_size).map_err(|e| CranelispError::CodegenError {
                message: format!("failed to mmap: {}", e),
                span: (0, 0),
            })?;
        mmap[..text_size].copy_from_slice(text_data);
        let base_addr = mmap.as_ptr() as usize;

        // Collect defined symbols from the text section.
        // sym.address() is a virtual address in the object file; subtract the text
        // section's own virtual address to get an offset into our mmap'd copy of
        // the section data. Previously this worked by accident because __text was
        // always at VA 0, but after switching the GOT from __bss to __data the
        // __data section occupies lower VAs and __text starts at a nonzero VA.
        let text_section_index = text_section.index();
        let text_section_addr = text_section.address();
        for sym in obj.symbols() {
            if sym.kind() != SymbolKind::Text {
                continue;
            }
            if sym.section_index() != Some(text_section_index) {
                continue;
            }
            if let Ok(name) = sym.name() {
                if !name.is_empty() {
                    // Strip leading underscore (Mach-O prefixes symbols with _)
                    let clean_name = name.strip_prefix('_').unwrap_or(name);
                    let offset_in_text = (sym.address() - text_section_addr) as usize;
                    let addr = base_addr + offset_in_text;
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
                            message: format!("bad relocation symbol: {}", e),
                            span: (0, 0),
                        }
                    })?;
                    let raw_name = sym.name().map_err(|e| CranelispError::CodegenError {
                        message: format!("bad symbol name: {}", e),
                        span: (0, 0),
                    })?;
                    // Strip Mach-O leading underscore
                    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
                }
                _ => {
                    return Err(CranelispError::CodegenError {
                        message: "unsupported relocation target".to_string(),
                        span: (0, 0),
                    });
                }
            };

            let raw_target_addr = self
                .defined_symbols
                .get(&target_name)
                .or_else(|| self.symbols.get(&target_name))
                .copied()
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("unresolved symbol: {}", target_name),
                    span: (0, 0),
                })?;

            let patch_addr = base_addr + offset as usize;
            let addend = reloc.addend();

            // For GOT-load relocations, redirect through a linker-internal GOT slot.
            // The code uses ADRP+LDR to load a pointer from the GOT entry,
            // so we need a cell in memory that contains the target address.
            let target_addr = match reloc.flags() {
                RelocationFlags::MachO { r_type, .. }
                    if r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGE21
                        || r_type == macho_arm64::ARM64_RELOC_GOT_LOAD_PAGEOFF12 =>
                {
                    let slot_addr = self.get_or_create_got_slot(&target_name, raw_target_addr);
                    slot_addr
                }
                _ => raw_target_addr,
            };

            match reloc.flags() {
                // Mach-O aarch64 relocations
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
                // ELF aarch64 relocations
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
                            "unsupported relocation flags {:?} for '{}'",
                            flags, target_name
                        ),
                        span: (0, 0),
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
                    span: (0, 0),
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
}

/// Apply a Mach-O aarch64 relocation.
fn apply_macho_arm64_reloc(
    mmap: &mut MmapMut,
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
        macho_arm64::ARM64_RELOC_BRANCH26 => {
            let rel_offset = (target_addr as i64 + addend - patch_addr as i64) >> 2;
            if !(-(1 << 25)..(1 << 25)).contains(&rel_offset) {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "branch target '{}' out of range: offset {}",
                        target_name, rel_offset
                    ),
                    span: (0, 0),
                });
            }
            let existing = u32::from_le_bytes(
                mmap[offset..offset + 4].try_into().unwrap(),
            );
            let patched =
                (existing & 0xFC00_0000) | ((rel_offset as u32) & 0x03FF_FFFF);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        // ARM64_RELOC_PAGE21: ADRP (21-bit page offset)
        macho_arm64::ARM64_RELOC_PAGE21
        | macho_arm64::ARM64_RELOC_GOT_LOAD_PAGE21 => {
            let target_page = ((target_addr as i64 + addend) >> 12) << 12;
            let patch_page = (patch_addr as i64 >> 12) << 12;
            let page_offset = ((target_page - patch_page) >> 12) as i32;

            let existing = u32::from_le_bytes(
                mmap[offset..offset + 4].try_into().unwrap(),
            );
            let immlo = ((page_offset as u32) & 0x3) << 29;
            let immhi = (((page_offset as u32) >> 2) & 0x7FFFF) << 5;
            let patched = (existing & 0x9F00_001F) | immhi | immlo;
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        // ARM64_RELOC_PAGEOFF12: ADD/LDR page offset (12-bit)
        macho_arm64::ARM64_RELOC_PAGEOFF12
        | macho_arm64::ARM64_RELOC_GOT_LOAD_PAGEOFF12 => {
            let page_off = ((target_addr as i64 + addend) & 0xFFF) as u32;
            let existing = u32::from_le_bytes(
                mmap[offset..offset + 4].try_into().unwrap(),
            );
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
                    "unsupported Mach-O ARM64 relocation type {} for '{}'",
                    r_type, target_name
                ),
                span: (0, 0),
            });
        }
    }
    Ok(())
}

/// Apply an ELF aarch64 relocation (for Linux targets).
fn apply_elf_aarch64_reloc(
    mmap: &mut MmapMut,
    offset: usize,
    patch_addr: usize,
    target_addr: usize,
    addend: i64,
    r_type: u32,
    target_name: &str,
) -> Result<(), CranelispError> {
    // ELF relocation type constants
    const R_AARCH64_CALL26: u32 = 283;
    const R_AARCH64_ADR_PREL_PG_HI21: u32 = 275;
    const R_AARCH64_ADD_ABS_LO12_NC: u32 = 277;
    const R_AARCH64_LDST64_ABS_LO12_NC: u32 = 286;
    const R_AARCH64_ABS64: u32 = 257;

    match r_type {
        R_AARCH64_CALL26 => {
            let rel_offset = (target_addr as i64 + addend - patch_addr as i64) >> 2;
            let existing = u32::from_le_bytes(
                mmap[offset..offset + 4].try_into().unwrap(),
            );
            let patched =
                (existing & 0xFC00_0000) | ((rel_offset as u32) & 0x03FF_FFFF);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        R_AARCH64_ADR_PREL_PG_HI21 => {
            let target_page = ((target_addr as i64 + addend) >> 12) << 12;
            let patch_page = (patch_addr as i64 >> 12) << 12;
            let page_offset = ((target_page - patch_page) >> 12) as i32;

            let existing = u32::from_le_bytes(
                mmap[offset..offset + 4].try_into().unwrap(),
            );
            let immlo = ((page_offset as u32) & 0x3) << 29;
            let immhi = (((page_offset as u32) >> 2) & 0x7FFFF) << 5;
            let patched = (existing & 0x9F00_001F) | immhi | immlo;
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        R_AARCH64_ADD_ABS_LO12_NC => {
            let page_off = ((target_addr as i64 + addend) & 0xFFF) as u32;
            let existing = u32::from_le_bytes(
                mmap[offset..offset + 4].try_into().unwrap(),
            );
            let patched = (existing & 0xFFC0_03FF) | ((page_off & 0xFFF) << 10);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        R_AARCH64_LDST64_ABS_LO12_NC => {
            let page_off = ((target_addr as i64 + addend) & 0xFFF) as u32;
            let existing = u32::from_le_bytes(
                mmap[offset..offset + 4].try_into().unwrap(),
            );
            let imm12 = (page_off >> 3) & 0xFFF;
            let patched = (existing & 0xFFC0_03FF) | (imm12 << 10);
            mmap[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
        }
        R_AARCH64_ABS64 => {
            let abs_val = (target_addr as i64 + addend) as u64;
            mmap[offset..offset + 8].copy_from_slice(&abs_val.to_le_bytes());
        }
        _ => {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "unsupported ELF aarch64 relocation type {} for '{}'",
                    r_type, target_name
                ),
                span: (0, 0),
            });
        }
    }
    Ok(())
}
