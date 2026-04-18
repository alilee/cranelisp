//! Global Offset Table (GOT) — re-exports from `cranelisp-types`.
//!
//! The `GotTable` type was moved into `cranelisp-types` in Sprint 56 Wave 0
//! (§9.8 G7 pull-forward) so `SymbolTable` can own the GOT directly. This
//! module preserves the public path `cranelisp_backend::got::GotTable` for
//! backward compatibility during the migration. Later sprints remove the
//! re-export.

pub use cranelisp_types::GotTable;
