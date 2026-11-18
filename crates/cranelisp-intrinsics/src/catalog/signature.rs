//! Derivation of a catalog row's `(param_count, has_return)` from its function's
//! type (`design/intrinsics/intrinsics-table.md` §2.1).
//!
//! [`catalog_row!`] casts the function to the row's stated pointer type, so a
//! row whose type disagrees with its function does not compile, and reads both
//! fields from [`CAbiSignature`], so the pair cannot disagree with the type.
//! [`poll_leaf_row!`] builds the address-only poll-leaf row (§2.2).
//!
//! This file names only `catalog::IntrinsicEntry` and `catalog::PollFn`: the
//! catalog's compile-fail cells compile it on its own against stand-ins.

/// A parameter type the backend may declare as `i64`: a 64-bit word on the
/// supported 64-bit targets. A narrower parameter would be misread.
pub(crate) trait AbiWord {}
impl AbiWord for i64 {}
impl AbiWord for usize {}
impl<T> AbiWord for *const T {}
impl<T> AbiWord for *mut T {}

/// A return type the backend may declare: an `i64` result, or none.
pub(crate) trait AbiReturn {
    const HAS_RETURN: bool;
}
impl AbiReturn for i64 {
    const HAS_RETURN: bool = true;
}
impl AbiReturn for () {
    const HAS_RETURN: bool = false;
}

/// The catalog signature of an `extern` function-pointer type.
pub(crate) trait CAbiSignature {
    const PARAM_COUNT: usize;
    const HAS_RETURN: bool;
}

macro_rules! impl_signature {
    ($count:expr; $($param:ident),*) => {
        impl_signature!(@one $count; [extern "C" fn]; $($param),*);
        impl_signature!(@one $count; [unsafe extern "C" fn]; $($param),*);
        impl_signature!(@one $count; [extern "C-unwind" fn]; $($param),*);
    };
    (@one $count:expr; [$($fn_ty:tt)+]; $($param:ident),*) => {
        impl<R: AbiReturn, $($param: AbiWord),*> CAbiSignature for $($fn_ty)+($($param),*) -> R {
            const PARAM_COUNT: usize = $count;
            const HAS_RETURN: bool = R::HAS_RETURN;
        }
        // A diverging function declares no result.
        impl<$($param: AbiWord),*> CAbiSignature for $($fn_ty)+($($param),*) -> ! {
            const PARAM_COUNT: usize = $count;
            const HAS_RETURN: bool = false;
        }
    };
}

impl_signature!(0;);
impl_signature!(1; A);
impl_signature!(2; A, B);
impl_signature!(3; A, B, C);
impl_signature!(4; A, B, C, D);

/// One catalog row:
/// `catalog_row!(name, path::to::function, fn-pointer type)`.
macro_rules! catalog_row {
    ($name:literal, $function:path, $fn_ty:ty $(,)?) => {
        $crate::catalog::IntrinsicEntry {
            name: $name,
            ptr: ($function as $fn_ty) as *const u8,
            param_count: <$fn_ty as $crate::catalog::signature::CAbiSignature>::PARAM_COUNT,
            has_return: <$fn_ty as $crate::catalog::signature::CAbiSignature>::HAS_RETURN,
        }
    };
}
pub(crate) use catalog_row;

/// The poll-leaf row: `poll_leaf_row!(name, path::to::function)`.
///
/// Admits a function only through a cast to `PollFn`, the ABI the trampoline
/// calls a poll node's `code_ptr` through. The `(3, true)` pair is the
/// uniform-word declaration the backend takes the leaf's address from; it
/// does not describe a call ABI, and emitted code never calls this row.
macro_rules! poll_leaf_row {
    ($name:literal, $function:path) => {
        $crate::catalog::IntrinsicEntry {
            name: $name,
            ptr: ($function as $crate::catalog::PollFn) as *const u8,
            param_count: 3,
            has_return: true,
        }
    };
}
pub(crate) use poll_leaf_row;
