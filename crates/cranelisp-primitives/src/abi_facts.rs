//! Private Rust-side ABI facts derived by the primitive declaration inventory.

#[cfg(test)]
use cranelisp_intrinsics::handle::Borrowed;
use cranelisp_intrinsics::handle::Owned;
use cranelisp_types::Type;

/// The Rust ownership shape used on one side of a raw primitive shim word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbiKind {
    Scalar,
    OwnedHandle,
}

/// Convert one raw ABI word to or from the private type written in a
/// declaration row.
pub(crate) trait AbiHandle: Sized {
    const KIND: AbiKind;

    /// Convert one raw wrapper argument to its declared private body type.
    ///
    /// # Safety
    ///
    /// The declaration's type must assign `raw` the ownership represented by
    /// `Self`.
    unsafe fn from_abi(raw: i64) -> Self;

    /// Convert a private body result back to the unchanged raw shim ABI.
    fn into_abi(self) -> i64;
}

impl AbiHandle for i64 {
    const KIND: AbiKind = AbiKind::Scalar;

    unsafe fn from_abi(raw: i64) -> Self {
        raw
    }

    fn into_abi(self) -> i64 {
        self
    }
}

impl AbiHandle for Owned {
    const KIND: AbiKind = AbiKind::OwnedHandle;

    unsafe fn from_abi(raw: i64) -> Self {
        // SAFETY: upheld by the declaration-derived wrapper contract above.
        unsafe { Owned::from_abi(raw) }
    }

    fn into_abi(self) -> i64 {
        self.into_raw()
    }
}

/// The one private adapter for a freshly produced, fully initialized runtime
/// result (or its specifically approved nullary/error sentinel).
///
/// # Safety
///
/// `raw` must be a fresh RC=1 runtime value whose initial reference transfers
/// to the caller, canonical produced `None`/`SNil`, or quote-sexp's existing
/// raw-zero error sentinel after `runtime_panic` records the error.
pub(crate) unsafe fn adopt_produced_value(raw: i64) -> Owned {
    // SAFETY: the caller establishes one of the produced-value cases above.
    unsafe { Owned::from_abi(raw) }
}

#[cfg(test)]
pub(crate) fn test_owned(raw: i64) -> Owned {
    // SAFETY: module fixtures call this only when transferring one live test
    // reference or a canonical nullary tag into a typed body/consumer.
    unsafe { <Owned as AbiHandle>::from_abi(raw) }
}

#[cfg(test)]
pub(crate) fn test_borrowed(raw: i64) -> Borrowed<'static> {
    // SAFETY: module fixtures keep the referenced raw allocation live for the
    // complete use of this returned test borrow.
    unsafe { Borrowed::from_abi(raw) }
}

/// Whether a declared language type travels as a counted heap handle.
pub(crate) fn is_heap_carried(ty: &Type) -> bool {
    !matches!(ty, Type::Int | Type::Bool | Type::Float)
}

#[cfg(test)]
pub(crate) fn abi_kinds_for(ty: &Type) -> Vec<AbiKind> {
    let Type::Fn(params, _) = ty else {
        panic!("primitive declaration must carry a function type");
    };
    params.iter().map(kind_of).collect()
}

#[cfg(test)]
pub(crate) fn result_kind_for(ty: &Type) -> AbiKind {
    let Type::Fn(_, result) = ty else {
        panic!("primitive declaration must carry a function type");
    };
    kind_of(result)
}

#[cfg(test)]
fn kind_of(ty: &Type) -> AbiKind {
    if is_heap_carried(ty) {
        AbiKind::OwnedHandle
    } else {
        AbiKind::Scalar
    }
}

#[cfg(test)]
mod tests;
