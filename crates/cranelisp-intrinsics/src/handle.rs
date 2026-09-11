//! Typed ownership vocabulary for counted runtime references.
//!
//! [`Owned`] represents one obligation to discharge or transfer a counted
//! reference. [`Borrowed`] is a read-only view whose safe constructor ties it
//! to the lifetime of an existing owner.

use std::marker::PhantomData;

/// One owned counted reference to a Cranelisp runtime value.
///
/// This wrapper is ABI-identical to the raw runtime word. It is deliberately
/// neither [`Copy`] nor [`Clone`]: moving it into a consuming operation records
/// the single discharge obligation in Rust's type system.
#[repr(transparent)]
#[must_use = "an Owned heap reference must be discharged (consumed, stored, or returned across the ABI shim) — dropping it on the floor leaks"]
pub struct Owned(i64);

impl Owned {
    /// Adopt a raw word whose owned reference has transferred to this frame.
    ///
    /// Nullary tags are valid owned values and carry no heap allocation.
    ///
    /// # Safety
    ///
    /// `raw` must represent one live transferred counted reference, or a valid
    /// bare nullary tag. The caller must not discharge the transferred
    /// reference after adoption.
    pub unsafe fn from_abi(raw: i64) -> Self {
        Self(raw)
    }

    /// Transfer this ownership obligation back to a raw ABI word.
    #[must_use]
    pub fn into_raw(self) -> i64 {
        let raw = self.0;
        std::mem::forget(self);
        raw
    }

    /// Borrow this reference for read-only runtime access.
    pub fn as_borrowed(&self) -> Borrowed<'_> {
        Borrowed(self.0, PhantomData)
    }

    /// Return the raw word for read-only layout access.
    pub fn raw_for_read(&self) -> i64 {
        self.0
    }

    /// Whether this value is a bare nullary tag rather than a heap pointer.
    pub fn is_nullary_tag(&self) -> bool {
        self.0 < cranelisp_types::NULLARY_TAG_THRESHOLD as i64
    }
}

#[cfg(debug_assertions)]
impl Drop for Owned {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            panic!(
                "LEAKED Owned heap handle {:#x} — dropped without discharge, storage, or ABI transfer",
                self.0
            );
        }
    }
}

/// A read-only view of a counted runtime reference.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Borrowed<'a>(i64, PhantomData<&'a ()>);

impl<'a> Borrowed<'a> {
    /// Assert a retained raw ABI reference for read-only access.
    ///
    /// # Safety
    ///
    /// `raw` must remain live for every use of the returned borrow, or be a
    /// valid bare nullary tag. The ABI caller owns that lifetime assertion.
    pub unsafe fn from_abi(raw: i64) -> Borrowed<'static> {
        Borrowed(raw, PhantomData)
    }

    /// Acquire a new counted reference from this live borrow.
    pub fn to_owned(self) -> Owned {
        crate::rc::rc_inc(self.0);
        // SAFETY: `rc_inc` just established the reference this value adopts;
        // bare nullary tags are valid and `rc_inc` intentionally leaves them
        // unchanged.
        unsafe { Owned::from_abi(self.0) }
    }

    /// Return the raw word for read-only layout access.
    pub fn raw_for_read(self) -> i64 {
        self.0
    }
}

#[cfg(test)]
pub(crate) fn test_owned(raw: i64) -> Owned {
    // SAFETY: test fixtures use this only where they deliberately model an ABI
    // transfer or another independently counted reference.
    unsafe { Owned::from_abi(raw) }
}

#[cfg(test)]
mod tests;
