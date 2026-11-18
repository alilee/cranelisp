//! The single ISA construction point, [`build_isa`] (re-exported at the crate
//! root as `cranelisp_backend::build_isa`), and the object-path tests.
//!
//! The object compilation path is `compile_to_module::<ObjectModule>` followed
//! by the caller's `obj_module.finish().emit()`; there is no separate
//! object-compile entry. See `design/backend/module-caching.md` §5 and §7.

use std::sync::Arc;

use cranelisp_types::{CranelispError, ErrorLocation, Span};

/// Build ISA for the host architecture.
///
/// Single ISA construction point (architecture decision 7, addresses HIGH-2).
/// - `is_pic: false` for JIT (absolute addresses)
/// - `is_pic: true` for ObjectModule (relocatable code)
pub fn build_isa(
    is_pic: bool,
) -> Result<Arc<dyn cranelift_codegen::isa::TargetIsa>, CranelispError> {
    use cranelift_codegen::settings::{self, Configurable};

    let mut flag_builder = settings::builder();
    flag_builder
        .set("use_colocated_libcalls", "false")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    flag_builder
        .set("is_pic", if is_pic { "true" } else { "false" })
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;

    let isa_builder = cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
        message: format!("host architecture not supported: {msg}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;

    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to build ISA: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })
}

#[cfg(test)]
mod tests;
