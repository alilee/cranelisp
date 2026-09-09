//! Private heap-ADT fixtures shared by the crate's integration-test binaries.
//!
//! The allocation exactly models the host contract:
//! `[total_size@0][rc@8][tag@16(u32)][pad@20][field_i@24+8i]`.
//! The header comes from [`cranelisp_types::HeapHeader`]; the payload shape
//! follows [`cranelisp_platform::HostCallbacks::alloc_with_tag`]'s five-step
//! contract. These helpers return and accept the allocation base, as `CLAdt`
//! does, and intentionally expose no production API.

use cranelisp_platform::HEAP_HEADER_SIZE;
use cranelisp_types::HeapHeader;

pub(crate) fn alloc_full_heap_adt(tag: u32, fields: &[i64]) -> i64 {
    let payload_size = 8 + fields.len() * 8;
    let total_size = HeapHeader::SIZE + payload_size;
    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
        let alloc_base = std::alloc::alloc_zeroed(layout);
        *(alloc_base as *mut i64) = total_size as i64;
        *((alloc_base as *mut i64).add(1)) = 1;
        let payload = alloc_base.add(HEAP_HEADER_SIZE as usize);
        *(payload as *mut u32) = tag;
        *(payload.add(4) as *mut u32) = 0;
        for (i, value) in fields.iter().enumerate() {
            *(payload.add(8 + i * 8) as *mut i64) = *value;
        }
        alloc_base as i64
    }
}

pub(crate) fn dealloc_heap_adt(base: i64) {
    unsafe {
        let total_size = *(base as *const i64) as usize;
        let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
        std::alloc::dealloc(base as *mut u8, layout);
    }
}

#[allow(dead_code)] // Shared module is compiled once per integration-test binary.
pub(crate) fn read_rc(base: i64) -> i64 {
    unsafe { *((base + 8) as *const i64) }
}
