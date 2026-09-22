//! User-callable Vec primitives — no Rust items.
//!
//! The Vec query family (`vec-get`, `vec-set`, `vec-push`, `vec-len`) is
//! declared as inline rows in the primitive declaration inventory and lowered
//! directly by the backend; it has no body, wrapper or GOT slot here. Vec
//! runtime representation lives in `cranelisp-intrinsics::vec_runtime`. This
//! module intentionally exports no Rust-callable implementation surface.
