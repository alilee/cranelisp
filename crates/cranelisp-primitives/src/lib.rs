//! Cranelisp primitives — synthetic-module entries for built-in operators.
//!
//! Per FIXME 0159 resolution: this crate's only public surface is
//! `PRIMITIVES_TABLE`, a `LazyLock<SymbolTable>` populated at static-init time
//! with `ModuleEntry::Def` entries for each primitive named by the spec.
//! The extern fn implementations are `pub(crate)` and reachable only via
//! `ModuleEntry::Def.got_slot` indexing into the synthetic primitives module's
//! GOT table.
//!
//! WAVE 2 SCAFFOLDING: this crate is currently empty. Content migration from
//! `cranelisp-runtime` is Wave 3b work (FIXME 0150 / D43 Phase 2-3).
