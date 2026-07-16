//! `cranelisp-backend` — typed AST → Cranelift IR → executable.
//!
//! Owns codegen, reference-count (RC) emission, JIT lifecycle, caching, and
//! linking. Paired with the backend-emitted runtime library (`cranelisp-primitives`
//! + `cranelisp-intrinsics`, the D43 split of the former `cranelisp-runtime`, whose
//! intrinsics the emitted CLIF calls). This crate is the only one that names Cranelift types; everything
//! upstream of it flows in through `cranelisp-types`.
//!
//! # The codegen boundary — exactly three free functions
//!
//! The entire public codegen surface consumed by the integration layer
//! (`int`) is three free functions plus the ISA constructor:
//!
//! - [`compile_to_module`] — the sole CLIF emission path. Generic over
//!   `M: Module + CodeFinalizer`: the same body emits byte-identical CLIF
//!   whether `M` is a `JITModule` (priority/REPL workers, per-symbol
//!   cardinality) or an `ObjectModule` (nice workers, per-module cardinality).
//!   **Mode is the `Module` instance the caller passes, never a parameter.**
//!   There is no separate object-compile entry — the object path is
//!   `compile_to_module::<ObjectModule>` followed by the **caller** finalising
//!   (`obj_module.finish().emit()`); see the §"Object file contract" notes in
//!   this source and the [`CodeFinalizer`] trait.
//! - [`load_object`] — the JIT-mode cache-hit entry. Constructs a fresh
//!   `cache::linker::Linker`, loads `.o` bytes into it, and returns a
//!   [`LinkerArtefact`] (the `Arc<Linker>` retention root + per-symbol address
//!   map).
//! - [`produce_disasm`] — on-demand machine-code disassembly (REPL `/disasm`).
//!   The caller supplies `code_size` (it received it in [`CompilationArtifacts`]);
//!   backend never re-derives it. Factored out of the always-created path
//!   because disassembly is far more expensive than the CLIF capture
//!   [`CompilationArtifacts`] carries unconditionally.
//! - [`build_isa`] — the single ISA construction point (re-exported from
//!   `cache::object::build_isa`).
//!
//! `symbol_tables` (a raw `&DashMap<ModuleFullPath, SymbolTable<C, L>>`) is the
//! single source for every codegen decision — callee/GOT-target resolution
//! (`compiler::resolve_got_target`), arity (`compiler::resolve_func_arity`),
//! `entry.kind` → dispatch shape, constructor metadata, and the per-module GOT
//! layout are all read from it; there is no side channel and no mode flag.
//!
//! # Who composes `Code` — the caller, both variants
//!
//! [`compile_to_module`] only **borrows** `&mut M`; it writes each compiled
//! symbol's fn pointer directly into the entry's GOT slot
//! (`symbol_table.got().store_slot(slot, ptr)`) and returns the always-created
//! introspection byproducts as [`CompilationArtifacts`]. It does **not**
//! construct the [`Code`] lifecycle owner — it cannot, because it never owns
//! the `Arc<Jit>`. The caller composes `Code::Jit` from its owned `Arc<Jit>`
//! after the call, symmetric with the cache-hit path where the caller composes
//! `Code::Linker` from the [`LinkerArtefact`] [`load_object`] returns. The GOT
//! is the single source of truth for callable addresses; [`Code`] carries
//! lifecycle ownership only (no `ptr` field).
//!
//! # The JIT construct boundary — `Jit::new(symbol_tables)`
//!
//! The JIT-mode caller (int) constructs a [`jit::Jit`] via the single
//! construct boundary `Jit::new(symbol_tables)` (BC §3 "Minimal JIT-setup
//! boundary"). The caller assembles **nothing**: the constructor derives the
//! entire JIT symbol set from the same `&SymbolTables<C, L>` that feeds codegen
//! — (1) the intrinsic Import targets from
//! `cranelisp_intrinsics::intrinsics_table()`, (2) one `__cranelisp_got_{M}` →
//! `got().base_ptr()` data symbol per module (via the types-crate
//! `got_data_symbol_name`), and (3) every `DefKind::PlatformEffect` jit-name →
//! GOT-slot ptr (walking defs + `Import` edges). The body is `<C, L>`-blind
//! (reads only `got`/`kind`/`got_slot`), preserving the Decision 0048
//! primitives dep-ban. After construction the caller hands off
//! `jit.jit_module()` to [`compile_to_module`] and holds `Arc<Jit>` for
//! lifecycle/reclaim (Decision 31). The legacy hand-assembly constructors
//! (`new_with_symbols`/`new_with_isa`) are `pub(crate)` — internal/test only.
//!
//! # The host-symbol escape hatch — `Jit::define_symbol`
//!
//! `Jit::new`'s derivation of the JIT symbol set from `symbol_tables` is the
//! default; for symbols whose body is neither codegen-emitted, bundled
//! (`cranelisp-primitives`), nor catalogued
//! (`cranelisp_intrinsics::intrinsics_table()`) — host-promised externs
//! (`DefKind::PrimitiveExtern`, BC §3 invariant 8 / §7 types) whose body lives
//! in `int` and reads live session state — [`jit::Jit::define_symbol`] is the
//! additive escape hatch. It inserts into the mutable map the JIT's
//! `symbol_lookup_fn` consults at finalize, so an unresolved `Linkage::Import`
//! relocation against the extern key settles to int's promised pointer. The
//! motivating member is `discover-tests`; a `DefKind::PrimitiveExtern` callee
//! lowers as a `Linkage::Import` against its key (the kind-driven call arm in
//! `compiler::apply`, resolved by `compiler::resolve_extern_target`). Canonical:
//! `design/arch/test-discovery.md` §6.
//!
//! # The platform-interface codegen role (BC §3, platform-interface.md)
//!
//! Backend owns three platform responsibilities (TARGET, user-ratified
//! 2026-06-07):
//!
//! - **The schema generator** ([`schema`]) — given a root type set + a
//!   `SymbolTable` map, computes the transitive closure of concrete ADT
//!   layouts and emits the schema artifact text + canonical layout hash
//!   ([`schema::generate_schema`] / [`schema::compute_layout_hash`]). It
//!   **shares the closure-walk + concrete-instantiation substitution** with the
//!   trace `DisplayDescriptor` baker (`compiler::trace_codegen`) — the shared
//!   asset is the *walk*, not the serialized output form. One generator, three
//!   callers: int's `/platform-schema` command, the session-load hash check,
//!   and the `--link` startup-object hash bake.
//! - **The platform GOT-indirect call arm** — a `DefKind::PlatformEffect` call
//!   site emits GOT-indirect dispatch against the DLL's exported
//!   `__cranelisp_got_platform_<name>` at the entry's `got_slot` (the new
//!   shape), structurally identical to user-module GOT dispatch; the as-built
//!   direct-extern-against-`jit_name` path stays live while `got_slot: None`
//!   (transitional discriminator: `compiler::resolve_got_target`). Backend does
//!   not emit the platform GOT (the DLL exports it).
//! - **Startup-object hash baking** — [`exe::PlatformLayoutCheck`] +
//!   `exe::generate_startup_object_checked` bake the compiler-computed layout
//!   hash + a `cranelisp_check_layout_hash` compare into the `--link` startup
//!   stub; mismatch aborts at process start with rebuild guidance.
//!
//! # Persistence
//!
//! The [`cache`] submodule is backend's persistence half — an internal
//! implementation mechanism, not a separate boundary surface. See its module
//! rustdoc for the four-submodule shape and the cache invariants.
//!
//! # Sealed traits
//!
//! None. Backend implements no traits from `cranelisp-types`. (`Module` is from
//! `cranelift-module`, not `cranelisp-types`.)

// `result_large_err`: pre-existing endemic lint (126 sites) — every fn that
// returns `Result<_, CranelispError>`. `CranelispError` is the workspace error
// type owned by `cranelisp-types`; boxing it (the lint's suggested fix) is a
// separate cross-crate `/arch` decision, not a backend-local change, and was
// NOT introduced by this sprint. Allowed at crate scope with rationale per the
// S75 W4 user decision (allow-with-rationale, NOT box-the-error).
#![allow(clippy::result_large_err)]

pub mod cache;

// Re-export build_isa at the crate root for convenient access.
// This is the single ISA construction point (architecture decision 7).
pub use cache::object::build_isa;
use cranelisp_types::ModuleEntry;
// Re-export TargetIsa for shared ISA in N-core codegen (pipeline-v3.md §6).
pub use cranelift::codegen::isa::TargetIsa;
// Re-export Cranelift module types for callers of compile_to_module.
pub use cranelift_module;
pub use cranelift_object;
pub mod codegen_types;
pub mod exe;
pub mod compiler;
pub mod got;
pub mod got_observer;
pub mod heap;
pub mod jit;
pub mod primitives_inline;
/// N3 (S105, `design/backend/ownership-codegen.md` §13.2.2): the gated,
/// backend-side per-site residual-atomic-RC dump (`[RC_SITE_STATS]`). Internal —
/// no public surface (codegen-time measurement counter, zero-cost-off).
mod rc_site_stats;

// Platform-interface schema generator (platform-interface.md §5.5/§6.0; BC §3
// "the platform-interface codegen role"). The single generator with multiple
// callers (int's `/platform-schema` command + session-load hash check; the
// `--link` startup-object hash bake). Shares the closure-walk + substitution
// with the trace `DisplayDescriptor` baker (`compiler::trace_codegen`).
pub mod schema;

// Per-symbol lifecycle owner (Decision 35 + Decision 41). Moved here from
// `src/code.rs` in Sprint 67 Wave 3 per the facade's S67 close-out — the
// enum's variants reference backend-owned `Arc<Jit>` / `Arc<Linker>`, so
// the enum belongs in backend. The integration layer imports it as
// `cranelisp_backend::Code` and uses it to instantiate
// `SymbolTable<Code, ()>`.
pub mod code;
pub use code::Code;

// Typed error DTOs for the backend public surface (Sprint 67 Wave 0 — REV-4).
// Per `facades/backend.md` §"Errors". `CompilationError` is the typed result of
// `compile_to_module`; `LinkerError` is the typed result of
// `Linker::get_symbol`. Consumer wiring lands in Wave 3 — these are authored
// here at Wave 0 so /dev (backend) and /dev (int) have a stable target type.
pub mod error;
pub use error::{CompilationError, LinkerError};

// Return-shape DTO for `load_object` — `LinkerArtefact`. `compile_to_module`
// has no artefact shape (it writes the GOT slot directly + returns
// `CompilationArtifacts` by value). `ObjectArtefact` is a not-currently-
// produced typed shape (see `artefact.rs` and the delete-candidate note
// there) — the object path returns `.o` bytes via the caller's
// `finish().emit()`, not through a backend-constructed artefact.
pub mod artefact;
pub use artefact::{LinkerArtefact, ObjectArtefact};

use std::collections::HashMap;

use cranelift_module::FuncId;

use dashmap::DashMap;

use cranelisp_types::{ErrorLocation,
    CranelispError, Defn, ModuleFullPath, Span, Symbol, SymbolTable,
};

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::compiler::{CompileContext, FnCompiler};
use crate::jit::declare_intrinsics_generic;

// --- CLIF dump observability (Sprint 60 Workstream B) --------------------
//
// `CRANELISP_CODEGEN_DUMP` selects which freshly-codegen'd CLIF is written
// to stderr during `compile_to_module`. This is load-bearing for diagnosing
// JIT/object divergence and codegen-layer bugs (drop glue, RC, GOT) where
// source-level reduction plateaus and only the emitted IR distinguishes
// correct vs broken output. Cache-hit paths do NOT re-codegen and so have
// nothing to dump; for those, use `/clif <name>` from the REPL to view the
// stored `FunctionArtifacts.clif_ir`.
//
// Filter grammar (value of `CRANELISP_CODEGEN_DUMP`):
//   unset/empty → disabled (no dump)
//   `*`         → dump every function in every module
//   `<module>`  → dump every function in that module (match on the
//                 `ModuleFullPath` string, e.g. `user`, `exemplar.solver`)
//   `<module>::<symbol>` → dump only that exact function
//
// Output: stderr, framed with `; === CLIF <module>::<symbol> ===` so it is
// greppable in test output. Shape mirrors what `/clif` prints in the REPL.

/// Decide whether to dump CLIF for a given (module, symbol) pair given the
/// current value of `CRANELISP_CODEGEN_DUMP`.
///
/// Pulled out as a pure function so unit tests can exercise the filter
/// grammar without any codegen side-effects.
fn clif_dump_matches(filter: Option<&str>, module_path: &str, symbol: &str) -> bool {
    let Some(filter) = filter.filter(|s| !s.is_empty()) else {
        return false;
    };
    if filter == "*" {
        return true;
    }
    if let Some((m, s)) = filter.split_once("::") {
        return m == module_path && s == symbol;
    }
    filter == module_path
}

/// Print a CLIF dump header + body to the provided writer. Extracted from the
/// call site so tests can capture output without intercepting stderr.
fn write_clif_dump(
    out: &mut dyn std::io::Write,
    module_path: &str,
    symbol: &str,
    clif_ir: &str,
) -> std::io::Result<()> {
    writeln!(out, "; === CLIF {module_path}::{symbol} ===")?;
    out.write_all(clif_ir.as_bytes())?;
    if !clif_ir.ends_with('\n') {
        writeln!(out)?;
    }
    writeln!(out, "; === end CLIF {module_path}::{symbol} ===")
}

/// Per-symbol codegen byproducts captured during `compile_to_module`.
///
/// Crate-internal lower-level record produced inside the per-symbol compile
/// loop (`compile_defn_in_module`). Aggregated into the public
/// `CompilationArtifacts` for the boundary return. Disassembly is **not**
/// captured here — it flows through the on-demand `produce_disasm` free
/// function instead (the always-created path carries only the cheap CLIF +
/// code-size byproducts; per the S70 Phase B amendment to Decision 41).
pub(crate) struct FunctionArtifacts {
    /// Human-readable CLIF dump of the compiled function. Same text rendered
    /// by `/clif`.
    pub clif_ir: String,
    /// Size in bytes of the compiled machine code.
    pub code_size: u32,
}

/// Always-created introspection artefacts returned by value from
/// `compile_to_module` (S70 Phase B amendment to Decision 41; FIXME 0221).
///
/// Backend writes each compiled symbol's fn pointer directly into its GOT
/// slot via `symbol_table.got().store_slot(slot, ptr)` (D41 #2) and returns
/// these introspection byproducts by value. The caller composes its
/// `Introspection` struct (REPL/trace mode → retain) or drops the artefact
/// (production batch). Backend never names int's `Introspection` (no DAG
/// inversion).
///
/// Every field is a free byproduct of the normal codegen flow (CLIF capture,
/// finalize-reported code size, wall-clock duration). The expensive
/// disassembly path is factored out into the separate on-demand
/// `produce_disasm` free function.
///
/// **Aggregation.** `compile_to_module` compiles the `names` it is given —
/// one symbol per call in JIT mode (per-symbol JIT cardinality, Decision 41),
/// the full module's defined symbols in object mode. The fields aggregate
/// across the compiled set: `clif_ir` is the concatenation of each function's
/// CLIF dump, `code_size` is the summed native code size, `compile_duration`
/// is the wall-clock span of the whole `compile_to_module` call.
#[non_exhaustive]
pub struct CompilationArtifacts {
    /// CLIF IR text. Concatenation of each compiled function's CLIF dump.
    pub clif_ir: String,
    /// Native code size in bytes, summed across the compiled set.
    pub code_size: usize,
    /// Wall-clock duration of the codegen step (parse-IR → finalized code).
    pub compile_duration: std::time::Duration,
}

/// Capability extension for the `Module` trait: post-finalize code access.
///
/// `cranelift_module::Module` does NOT expose `finalize_definitions` or
/// `get_finalized_function` — those are inherent methods on specific
/// implementations (`JITModule`) and absent from others (`ObjectModule`,
/// whose output is bytes via `finish().emit()`, not runtime pointers).
///
/// Per `design/backend/compile-to-module.md` §9.1.6 and `/arch` Decision 23,
/// the JIT/Object split is a capability difference expressed on the `Module`
/// implementation — not a mode parameter on `compile_to_module`. This trait
/// provides that capability: `JITModule` implements it with the real
/// operations; `ObjectModule` implements it with no-ops that surface `None`
/// so the G6 write loop skips the per-entry pointer store in object mode.
///
/// Any new `Module` implementation that `compile_to_module` is asked to
/// target must provide an impl — either the "real" one (if it has runtime
/// code pointers) or a no-op stub (if it has no post-finalize pointer, e.g.,
/// an emitter that produces bytes).
pub trait CodeFinalizer {
    /// Finalize pending definitions so that code pointers become readable.
    /// For `JITModule`: patches relocations, makes mmap'd pages executable.
    /// For `ObjectModule`: no-op (bytes are emitted via a later `finish()`).
    ///
    /// Called once per `compile_to_module` invocation after all `define_function`
    /// calls complete. Implementations that cannot finalize (e.g., already
    /// finalized) should return an error, not silently succeed.
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError>;

    /// Read a finalized code pointer for the given `FuncId`, if this module
    /// exposes runtime pointers. Returns `None` on implementations that have
    /// no such concept (`ObjectModule`), which gates the G6 write loop to JIT
    /// mode only (per §9.1.6).
    ///
    /// Only valid after `finalize_for_code_read()` has returned `Ok`.
    fn try_get_finalized_function(&self, func_id: FuncId) -> Option<*const u8>;

    /// Define the per-module GOT data symbol (`__cranelisp_got_{M}`) inside
    /// the module's `.o` artefact, with relocation initializers against each
    /// of the module's local function symbols. Implements the `.o` data
    /// section GOT half of the two-GOT model (`/arch` Decision 23 + 36).
    ///
    /// Parameters:
    /// - `name`: the `__cranelisp_got_{flat_path}` data symbol name
    ///   (single source of truth: `compiler::got_data_symbol_name`).
    /// - `slot_count`: total slot count = `max(slot_index) + 1`. The data
    ///   symbol is sized as `slot_count * 8` bytes (zero-initialized).
    /// - `slot_funcs`: `(slot_index, FuncId)` pairs for every defined
    ///   function in this module. Each slot's 8-byte entry receives a
    ///   relocation initializer pointing to that function's local symbol.
    ///   Slots with no entry remain zero (empty slots are not currently
    ///   produced by typecheck — every defined function gets a slot).
    ///
    /// For `JITModule`: no-op. The JIT-mode `__cranelisp_got_{M}` data is
    /// defined by the integration layer via `Jit::define_got_data` directly,
    /// pointing at the runtime `SymbolTable.got.base_ptr()`. The `.o` data
    /// definition is irrelevant in JIT mode (no `.o` is emitted).
    ///
    /// For `ObjectModule`: declares the symbol as `Linkage::Export`,
    /// allocates `slot_count * 8` bytes initialized to zero, and writes a
    /// function-address relocation at byte offset `slot_index * 8` for each
    /// `(slot_index, FuncId)` pair. The system linker (`--link` mode) and
    /// our cache `Linker` (`--run` mode after cache-hit) materialise these
    /// relocations into actual function addresses at load time.
    ///
    /// Per Decision 23: the same CLIF emitted by `compile_to_module<M>`
    /// references `__cranelisp_got_{M}` symmetrically as `Linkage::Import`
    /// in both modes; the *definition* differs by `Module` impl. JIT mode's
    /// definition lives outside `compile_to_module` (in the integration
    /// layer's `Jit::define_got_data` call); object mode's definition lives
    /// in this trait method, called from inside `compile_to_module`.
    fn define_module_got_data(
        &mut self,
        name: &str,
        slot_count: usize,
        slot_funcs: &[(usize, FuncId)],
    ) -> Result<(), CranelispError>;
}

impl CodeFinalizer for cranelift_jit::JITModule {
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError> {
        self.finalize_definitions().map_err(|e| CranelispError::CodegenError {
            message: format!("failed to finalize JIT definitions: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })
    }

    fn try_get_finalized_function(&self, func_id: FuncId) -> Option<*const u8> {
        Some(self.get_finalized_function(func_id))
    }

    fn define_module_got_data(
        &mut self,
        _name: &str,
        _slot_count: usize,
        _slot_funcs: &[(usize, FuncId)],
    ) -> Result<(), CranelispError> {
        // No-op: the JIT-mode `__cranelisp_got_{M}` data symbol is defined
        // by the integration layer's `Jit::define_got_data` call (which
        // points the symbol at the runtime SymbolTable.got.base_ptr()). The
        // `.o` data section GOT shape is unused in JIT mode — no `.o` is
        // emitted. See `/arch` Decision 23 (two-GOT model).
        Ok(())
    }
}

impl CodeFinalizer for cranelift_object::ObjectModule {
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError> {
        // No-op: ObjectModule output is bytes via `finish().emit()`, not
        // runtime code pointers. Finalization happens at byte-emit time, not
        // here. See §9.1.6 of compile-to-module.md.
        Ok(())
    }

    fn try_get_finalized_function(&self, _func_id: FuncId) -> Option<*const u8> {
        // No runtime pointer exists for object-mode compilation. The G6 write
        // loop skips the per-entry code write when this returns None.
        None
    }

    fn define_module_got_data(
        &mut self,
        name: &str,
        slot_count: usize,
        slot_funcs: &[(usize, FuncId)],
    ) -> Result<(), CranelispError> {
        // Bug B fix per `/arch` Decision 23 (updated Sprint 58 Wave 2):
        // declare the per-module GOT data symbol as `Linkage::Export` and
        // populate its slots with function-address relocations against each
        // defined function's local symbol. The system linker (`--link` mode)
        // and our cache `Linker` (`--run` mode after cache-hit) resolve the
        // relocations at load time, materialising the GOT contents.
        if slot_count == 0 {
            // No slots to define. Skip — symbol is not needed by callers.
            return Ok(());
        }

        // `writable = true` so the GOT atom lands in a WRITABLE section
        // (`__DATA`, not the read-only `__DATA_CONST`). The `(trace …)` GOT
        // copy-swap (`cranelisp_trace_swap_got`) installs the debug GOT over
        // the real GOT with a runtime `memcpy` INTO the GOT base — a store that
        // segfaults if the atom is in `__DATA_CONST` (dyld maps it read-only).
        // This mirrors the JIT runtime `GotTable` (a writable heap allocation)
        // — mode parity, Principles 11–13 (FIXME 0275). Normal call dispatch
        // only READS the GOT, so the writable placement is observationally
        // transparent outside tracing.
        let data_id = self
            .declare_data(name, cranelift_module::Linkage::Export, true, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!(
                    "failed to declare GOT data symbol '{name}' as Export: {e}"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;

        let mut desc = cranelift_module::DataDescription::new();
        // GOT atoms hold pointer-sized (8-byte) function-address slots, and
        // the `desc.write_function_addr` relocations declared below assume
        // pointer alignment. `DataDescription::new()` defaults to alignment
        // 1; macOS `ld` rejects unaligned atoms carrying pointer-sized
        // relocations ("warning: alignment (1) of atom ... is incompatible
        // ..." → linker error). Set explicit 8-byte alignment so the atom
        // lands at a pointer-aligned address.
        desc.set_align(8);
        // Use `define` with explicit zero bytes (NOT `define_zeroinit`) so the
        // GOT lands in a regular `__DATA` section, not `__DATA,__bss`
        // (`S_ZEROFILL`). macOS `ld` segfaults when applying relocations
        // against BSS sections — relocations require a regular data section.
        // The contents are identical (zero-initialized 8 bytes per slot) but
        // the section placement differs. Function-address relocations declared
        // below via `desc.write_function_addr` are still applied normally at
        // link time.
        //
        // Slab SIZE is the full `GOT_TABLE_SIZE` (NOT the live `slot_count`),
        // matching the runtime `GotTable`'s fixed `GOT_TABLE_SIZE`-slot
        // allocation (FIXME 0275 — mode parity, Principles 11–13). The
        // `(trace …)` GOT copy-swap (`cranelisp_trace_swap_got`) memcpy's a
        // fixed `GOT_TABLE_SIZE * 8` bytes from the GOT base in EVERY mode; in
        // JIT mode the base is the runtime full-size `GotTable`, so the swap is
        // in-bounds. If the object-mode slab were sized to `slot_count` only,
        // the same memcpy would read past the end of the `.o` GOT atom and
        // SIGBUS in `--link` binaries. Sizing the object slab to match the
        // runtime table closes that divergence; the trailing slots are
        // zero-filled and carry no relocation (cost: a fixed
        // `GOT_TABLE_SIZE * 8` = 8 KiB per module's `.o` GOT atom).
        let slab_slots = cranelisp_types::GOT_TABLE_SIZE.max(slot_count);
        desc.define(vec![0u8; slab_slots * 8].into_boxed_slice());

        for &(slot, func_id) in slot_funcs {
            // Sanity: slot must be in range; defensive guard against a
            // malformed slot list. A slot >= slot_count would corrupt
            // adjacent data; we surface the shape mismatch as an error
            // rather than silently truncate.
            if slot >= slot_count {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "GOT slot {slot} for '{name}' exceeds declared slot_count {slot_count}"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
            let func_ref = self.declare_func_in_data(func_id, &mut desc);
            let offset: u32 = (slot * 8).try_into().map_err(|_| {
                CranelispError::CodegenError {
                    message: format!(
                        "GOT slot offset overflows u32 for slot {slot} in '{name}'"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                }
            })?;
            desc.write_function_addr(offset, func_ref);
        }

        self.define_data(data_id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define GOT data symbol '{name}': {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        Ok(())
    }
}

/// Compile the functions named by `names` (all inside `module_path`) into a
/// Cranelift module.
///
/// This is the ONLY compilation entry point in the backend crate.
/// See design/backend/compile-to-module.md §2 (PRESCRIPTIVE).
///
/// The `capture_clif` flag (FIXME 0325) controls whether the CLIF-IR text
/// (`format!("{}", func.display())`) is rendered into the returned
/// `CompilationArtifacts.clif_ir`. The int layer sets it `true` only when
/// introspection is live (REPL/trace mode); in `--run`/`--link` batch it is
/// `false` and the CLIF-text allocation is skipped — the rendered string is
/// dropped unread there. The `CRANELISP_CODEGEN_DUMP` stderr dump path is
/// independent of this flag: it has its own per-symbol env-var trigger and
/// renders the CLIF for matching symbols regardless of `capture_clif`. The
/// `code_size` byproduct flows back unconditionally.
///
/// Parameters derived internally:
/// - Intrinsics: declared on the module internally
/// - Defn bodies: read from `symbol_tables[module_path].get(name).ast`
/// - GOT slots: read from `ModuleEntry::Def.got_slot`
/// - GOT base resolution: uniform — emits `global_value` against a
///   `Linkage::Import` data symbol `__cranelisp_got_{module}`; `Module`
///   implementations resolve at finalize time (linker relocations for Object;
///   `JITBuilder::symbol_lookup_fn` for JIT — caller's responsibility)
/// - Cross-module function refs: under `/arch` Decision 36 (bare-Local)
///   plus Decision 31 (all-GOT calling), every cross-module call is GOT-
///   indirect (`__cranelisp_got_{other_M}`). No `Linkage::Import` function
///   declarations are needed for cross-module fns — they are unreachable
///   by direct call. Compile-time arity for cross-module calls is resolved
///   via `compiler::resolve_func_arity` walking the symbol tables.
///
/// # Function naming and linkage (`/arch` Decision 36)
///
/// Every user-defined function is declared with its bare symbol-table name
/// (`defn.name`) and `Linkage::Local`, uniformly across all modules. The
/// pre-Sprint-58 `user`/`main` special case (bare-Export for those modules,
/// FQ-Export for everything else) was a defect, deleted here. Function
/// symbols never cross `.o` boundaries — every call goes through the per-
/// module GOT — so `Linkage::Local` is sufficient and avoids cross-`.o`
/// symbol-table pollution. See Decision 36 in `design/arch/CLAUDE.md` and
/// `design/backend/compile-to-module.md` §7 for the full rationale.
///
/// # G6 write path
///
/// After `define_function` completes for every name in `names`, the function
/// calls `module.finalize_for_code_read()` and — for JIT-capable modules —
/// reads each finalized code pointer and writes it onto the corresponding
/// `ModuleEntry::Def.code` in `symbol_tables[module_path]` before returning.
/// For `ObjectModule`, the capability call returns `None` and the write loop
/// is skipped (no runtime pointer exists). See §9.1 of
/// `design/backend/compile-to-module.md` and `/arch` Decision 25 for the
/// architectural statement.
///
/// # GOT data symbol emission (`/arch` Decision 23 Bug B fix)
///
/// After function declarations, this function calls
/// `module.define_module_got_data(...)` to emit the per-module
/// `__cranelisp_got_{M}` data symbol. The implementation is `Module`-impl-
/// specific:
/// - `JITModule`: no-op (the JIT path defines this symbol externally via
///   `Jit::define_got_data` pointing at the runtime
///   `SymbolTable.got.base_ptr()`).
/// - `ObjectModule`: declares the symbol as `Linkage::Export` with a
///   zero-initialized slab of `slot_count * 8` bytes and writes a function-
///   address relocation at byte offset `slot * 8` for each defined
///   function. The system linker (`--link`) and the cache `Linker` (`--run`
///   after cache-hit) resolve the relocations at load time.
pub fn compile_to_module<M, C, L>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    module: &mut M,
    capture_clif: bool,
) -> Result<CompilationArtifacts, CompilationError>
where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // Internal helper preserves the legacy `CranelispError` flow so the
    // codegen body (with ~40 `CranelispError::CodegenError { ... }` sites)
    // doesn't need a row-by-row rewrite. The `From<CranelispError> for
    // CompilationError` bridge in `error.rs` collapses internal errors into
    // `CompilationError::CodegenFailed { cause: <message> }` at the
    // boundary. See `facades/backend.md` §"Errors" for the contract.
    compile_to_module_impl::<M, C, L>(
        module_path,
        names,
        symbol_tables,
        module_aliases,
        module,
        capture_clif,
    )
    .map_err(CompilationError::from)
}

/// Build a `MonoExpr` from a body `Expr`, tolerating non-concrete node types —
/// the LENIENT counterpart of the strict, choke-pointed
/// [`cranelisp_types::MonoExpr::from_expr`].
///
/// **W0.b retired the live-path use** (`design/arch/backend-keyed-consumer.md`
/// §4 W0.b / §5): typecheck is the sole mono-view producer, so
/// `compile_to_module` no longer rebuilds a lenient view — a codegen-reached
/// body with `codegen_view: None` is a hard error. The ONLY surviving caller is
/// the `#[cfg(test)]`-reachable `jit.rs::compile_defn` unit helper (design §5
/// finding 3 — no live caller; W3 migrates it onto a typecheck-/`from_expr`-built
/// view and deletes this entry point + `lenient_from_expr`). The builder body
/// itself lives in `cranelisp-types` beside `from_expr` so view construction has
/// ONE home. The sidecars are empty here (the test helper lowers a bare
/// template); byte-identical to the former in-crate body.
pub(crate) fn lenient_mono_from_expr(
    expr: &cranelisp_types::Expr,
    resolved_targets: &std::collections::HashMap<cranelisp_types::Span, cranelisp_types::FQSymbol>,
) -> cranelisp_types::MonoExpr {
    use std::collections::HashMap;
    // W1 (KC-W0-6): the unit-test harness threads the dispatch carriers it
    // computes directly from the tables it also builds — a lenient-built body
    // now reaches W1's keyed reads (`entry_at`), so a `None` carrier would
    // hard-miss. Live `compile_to_module` consumes the typecheck-populated
    // `codegen_view` instead; this backend lenient path is test-harness-only
    // (jit.rs §5, no live caller) and deletes in W3.
    cranelisp_types::MonoExpr::lenient_from_expr(expr, &HashMap::new(), resolved_targets)
}

fn compile_to_module_impl<M, C, L>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_aliases: &cranelisp_types::ModuleAliases,
    module: &mut M,
    capture_clif: bool,
) -> Result<CompilationArtifacts, CranelispError>
where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let compile_start = std::time::Instant::now();
    // Derive internal dependencies.
    let intrinsic_ids = declare_intrinsics_generic(module)?;

    // Step 1: Look up each named entry and retrieve its AST body (§4 symbol-
    // table lookup loop; replaces the former `program: &Program` scan).
    // Wave 0 invariant: each entry in `names` carries `ast: Some(_)`. If not,
    // surface a codegen error naming the offending symbol — see
    // design/backend/compile-to-module.md §16.4.
    let mut defns: Vec<Defn> = Vec::with_capacity(names.len());
    // S84 Phase 3 (concrete-boundary-type.md §3.1, FIXME 0391): the codegen walk
    // is over `MonoExpr`. For each `UserFn { Concrete{slot} }` entry the body
    // comes from the typecheck-populated `codegen_view` (every node already a
    // `ConcreteType`), NOT reconstructed from `ast`. Carried in lockstep with
    // `defns`.
    let mut bodies: Vec<cranelisp_types::MonoExpr> = Vec::with_capacity(names.len());
    // The compile-in-hand ownership summary for each body (B3.2), read from the
    // same `codegen_view` the body comes from. `None` on the lenient fallback
    // (no view) and whenever the ownership analysis did not run
    // (`CRANELISP_NO_OWNERSHIP` ⇒ typecheck emits no summaries). Carried in
    // lockstep with `bodies`.
    let mut summaries: Vec<Option<cranelisp_types::ModeSummary>> =
        Vec::with_capacity(names.len());
    {
        let table = symbol_tables.get(&module_path).ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!(
                    "compile_to_module: no symbol table for module '{module_path}'"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        for name in names {
            let entry = table.get(name.as_ref()).ok_or_else(|| {
                CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: symbol '{name}' not found in module '{module_path}'"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                }
            })?;
            let ModuleEntry::Def { ast, visibility, docstring, codegen_view, .. } = entry else {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: symbol '{name}' in module '{module_path}' is not a compilable Def (wrong ModuleEntry variant)"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            let variant = ast.as_ref().ok_or_else(|| CranelispError::CodegenError {
                message: format!(
                    "compile_to_module: symbol '{name}' in module '{module_path}' has ast: None — Wave 0 invariant violated (see design/typecheck/ast-annotation.md for the categories of entries that must carry ast: Some(_))"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
            // The symbol-table entry stores the meaningful payload as a single
            // `DefnVariant` (S69 Sub 35). The backend codegen path is keyed on
            // `Defn`; reconstruct the single-variant `Defn` from the variant +
            // the entry's own name / visibility / docstring (the canonical
            // sources for that metadata post-narrowing). The `Defn` supplies the
            // signature (params / name / span) for declaration + binding; the
            // body walk uses the `MonoExpr` below.
            let defn = Defn {
                name: name.clone(),
                docstring: docstring.clone(),
                variants: vec![variant.clone()],
                visibility: *visibility,
                span: variant.span,
            };

            // The backend codegen walk is over `MonoExpr` (concrete-boundary-type.md
            // §3.1, FIXME 0391): every node carries a `ConcreteType`, so no
            // `Type::Var` reaches codegen and `HeapCategory::classify` is total over
            // `ConcreteType` (the `Var` arm is structurally deleted). The arc's
            // payoff is delivered HERE — the body the backend walks is a `MonoExpr`,
            // built through the `Expr → MonoExpr` choke point so `classify` can only
            // ever see a `ConcreteType`.
            //
            // **Body source: the typecheck-populated `codegen_view` on the live
            // concrete-defn path (S84, FIXME 0394/0395 — closed).** When the entry
            // carries a populated view (ordinary concrete defns + mono instances —
            // the body-AST-node-typed codegen targets), the body is the
            // `MonoDefnVariant.body: MonoExpr` typecheck built POST-mono: FIXME 0394
            // moved the `codegen_view` rebuild into the post-mono re-annotation seam
            // (`program.rs` finalize Step-1b), so the view's call nodes carry the
            // correct `SigDispatch{mangled}` dispatch (e.g. `(id 7)`'s `id` call →
            // `SigDispatch{id$Int}`). The dual-source FIXME 0395 forecloses
            // (populated-but-unread view + `ast`-rebuild) collapses to ONE source
            // here for every entry that HAS a view (Principle 7) — the SSOT.
            //
            // **Lenient fallback when the view is `None`.** A small set of
            // `Concrete{slot}` entries are body-AST-walked but legitimately carry
            // NO view: synthesised field accessors (`(match self [(Point _ y) y])`
            // — a synthetic `Match` whose nodes are `inferred_type: None`; the
            // backend reads field types from the ctor signature, not body node
            // types), and the §3.11.1-best-effort concrete-defn cases. These — plus
            // the signature-driven / generic / REPL-`__expr` entries
            // (`requires_codegen_view == false`) — fall through to the lenient
            // builder, whose residual `Var`/un-annotated nodes are read only via
            // `signature_heap_category` (Var→Mixed), never `classify`. Because the
            // lenient builder shares the `ConcreteType::from_type` choke point with
            // the strict view, the structural guarantee (no `Type::Var` reaches
            // `classify`) holds on BOTH paths.
            // **W0.b totalization flip (`backend-keyed-consumer.md` §4 W0.b /
            // §5, Principle 18).** typecheck is the SOLE mono-view producer for
            // EVERY codegen-reached body — ordinary concrete defns, mono
            // instances, ctor/accessor synthetic bodies, `f$Var` multi-sig
            // variants, `__expr`, macro-clause bodies. The `requires_codegen_view`
            // bypass and the backend lenient rebuild (`lenient_mono_from_expr`)
            // are retired from the live path: a codegen-reached entry with NO
            // typecheck-populated `codegen_view` is a producer gap and a HARD
            // error, never a silent lenient rebuild (Rev-2: no soft fallback).
            let (body, mode_summary) = match codegen_view {
                Some(view) => (view.body.clone(), view.mode_summary.clone()),
                None => {
                    return Err(CranelispError::CodegenError {
                        message: format!(
                            "compile_to_module: codegen-reached body '{name}' in module \
                             '{module_path}' has no typecheck-populated codegen_view. Post-W0.b \
                             typecheck is the sole mono-view producer (design/arch/\
                             backend-keyed-consumer.md §4 W0.b/§5); a None here is a producer \
                             gap (Principle 18), never a silent lenient rebuild."
                        ),
                        location: ErrorLocation::from_span(variant.span),
                    });
                }
            };

            defns.push(defn);
            bodies.push(body);
            summaries.push(mode_summary);
        }
    }

    // v9 ctx-vtable (`io-trampoline.md §17.3`): the S96 `inject_poll_leading_pair`
    // poll-shape operand-injection pass is DELETED. Under the ctx-vtable handle model
    // the platform poll-fn computes its token from the handle it holds and calls
    // `ctx.acquire` itself — there is no leading `(token, capacity)` pair to prepend,
    // so `compile_poll_effect` takes a poll leaf's natural args as `arg_vals[0..]`.

    if defns.is_empty() {
        return Err(CranelispError::CodegenError {
            message: "no function definitions to compile".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Step 2: Declare all functions in the module (Pass 1).
    // Start with intrinsic FuncIds.
    let mut func_ids: HashMap<Symbol, FuncId> = intrinsic_ids.by_name.clone();

    // Per `/arch` Decision 36: every user-defined function is declared with
    // its bare symbol-table name and `Linkage::Local`, uniformly across all
    // modules. The pre-Sprint-58 user/main vs FQ-Export discriminator is a
    // defect (see Decision 36 rationale + design/backend/compile-to-module.md
    // §7). Function symbols are intra-`.o`-only because all calls go through
    // `__cranelisp_got_{M}` (Decision 31 redefinition correctness mandates
    // GOT-indirect even for intra-module calls).
    for defn in &defns {
        let mut sig = module.make_signature();
        for _ in defn.params() {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = module
            .declare_function(defn.name.as_ref(), cranelift_module::Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare function '{}': {e}", defn.name),
                location: ErrorLocation::from_span(defn.span),
            })?;
        func_ids.insert(defn.name.clone(), func_id);
    }

    // No cross-module function declarations: under all-GOT calling
    // (Decision 31) cross-module calls are GOT-indirect against
    // `__cranelisp_got_{other_M}`, never direct. Compile-time arity for
    // those calls is resolved via `compiler::resolve_func_arity` walking
    // the symbol tables (see compiler/control_flow.rs auto-curry path).
    let func_arities: HashMap<Symbol, usize> = defns
        .iter()
        .map(|d| (d.name.clone(), d.params().len()))
        .collect();

    // Step 3: Compile each function body (Pass 2).
    // All defns are compiled uniformly — mangled multi-sig variants and mono
    // specialisations are ordinary entries in `names` after Wave 0.
    let mut func_ctx = FunctionBuilderContext::new();
    // Aggregate introspection byproducts across the compiled set into the
    // value-returned `CompilationArtifacts` (S70 Phase B amendment to D41).
    // `clif_ir` concatenates each function's dump; `code_size` sums the
    // native code sizes. The expensive `disasm` per-fn capture is discarded
    // here — it is re-derived on demand by `produce_disasm`.
    let mut clif_ir_agg = String::new();
    let mut code_size_agg: usize = 0;

    // Read CLIF dump filter once per compile_to_module invocation — the env
    // var value is stable for the process lifetime and this loop may iterate
    // many times.
    let clif_dump_filter: Option<String> = std::env::var("CRANELISP_CODEGEN_DUMP").ok();

    for ((defn, body), mode_summary) in defns.iter().zip(bodies.iter()).zip(summaries.iter()) {
        let compile_ctx = CompileContext {
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables,
            module_aliases,
            current_module: module_path.clone(),
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc.unwrap_or_else(|| {
                unreachable!(
                    "invariant: runtime/dealloc must be declared before compile \
                     (Decision 24)"
                )
            }),
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };
        // FIXME 0325: render the CLIF-IR text only when it will be consumed —
        // either the caller wants it captured into `CompilationArtifacts`
        // (`capture_clif`, REPL/trace introspection) or the env-gated stderr
        // dump path matches this symbol (its own independent trigger). In
        // `--run`/`--link` batch with introspection off and no dump filter,
        // both are false and the `format!("{}", func.display())` allocation is
        // skipped entirely.
        let dump_this =
            clif_dump_matches(clif_dump_filter.as_deref(), module_path.as_ref(), defn.name.as_ref());
        let render_clif = capture_clif || dump_this;
        let art = compile_defn_in_module(
            defn,
            body,
            mode_summary.clone(),
            module,
            &mut func_ctx,
            &func_ids,
            compile_ctx,
            render_clif,
        )?;
        if dump_this {
            // Write directly to stderr; ignore I/O errors (stderr failure is
            // not worth poisoning a codegen result over).
            let _ = write_clif_dump(
                &mut std::io::stderr(),
                module_path.as_ref(),
                defn.name.as_ref(),
                &art.clif_ir,
            );
        }
        if capture_clif {
            if !clif_ir_agg.is_empty() {
                clif_ir_agg.push('\n');
            }
            clif_ir_agg.push_str(&art.clif_ir);
        }
        code_size_agg += art.code_size as usize;
        // `art.disasm` deliberately dropped — on-demand via `produce_disasm`.
    }

    // Step 4a (`/arch` Decision 23 Bug B fix): emit the per-module GOT data
    // symbol `__cranelisp_got_{M}`. For ObjectModule this defines a
    // `Linkage::Export` data symbol with relocation initializers against
    // each defined function's local symbol; for JITModule this is a no-op
    // because the JIT-mode definition lives outside `compile_to_module`.
    // See `define_module_got_data` impls and §5.4 of compile-to-module.md.
    {
        let table = symbol_tables.get(&module_path).ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!(
                    "compile_to_module: no symbol table for module '{module_path}' at GOT-data emission"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        let mut slot_funcs: Vec<(usize, FuncId)> = Vec::with_capacity(defns.len());
        for defn in &defns {
            let entry = table.get(defn.name.as_ref()).ok_or_else(|| {
                CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: symbol '{}' missing from module '{module_path}' at GOT-data emission",
                        defn.name
                    ),
                    location: ErrorLocation::from_span(defn.span),
                }
            })?;
            // The GOT slot now rides on the callable `DefKind` variant
            // (S83 Option-A reshape); read it through the SSOT accessor.
            let Some(slot) = entry.callable_got_slot() else {
                continue; // Non-Def / slot-less Def (primitive-shaped, etc.)
            };
            let Some(&func_id) = func_ids.get(&defn.name) else {
                continue; // Defensive: can't happen — we declared it above
            };
            slot_funcs.push((slot, func_id));
        }
        let slot_count = table.next_got_slot;
        // Drop the read guard before potentially mutating other tables.
        drop(table);

        let got_name = crate::compiler::got_data_symbol_name(&module_path);
        module.define_module_got_data(&got_name, slot_count, &slot_funcs)?;
    }

    // Step 4: Finalize definitions.
    // For JITModule: patches relocations, makes code pages executable.
    // For ObjectModule: no-op (bytes emitted at a later `finish()` call).
    module.finalize_for_code_read()?;

    // Step 5 (D41 #2 — per-symbol GOT slot direct-write): for each compiled
    // symbol, read its finalised code pointer and write it directly into the
    // entry's GOT slot via `symbol_table.got().store_slot(slot, ptr)`. The
    // GOT is the single source of truth for callable addresses (Decision 35
    // post-rollback; facade §"Code"). Backend owns this write per the S70
    // Phase B amendment to Decision 41 — `compile_to_module` no longer
    // returns per-symbol `code_ptrs` for the caller to store.
    //
    // The lifecycle-owner write (D41 #1 — `Code::Jit(Arc<Jit>)` via
    // `write_code`) stays in the integration layer for now: backend receives
    // a generic `&mut M: Module` and does not own the `Arc<Jit>` (the caller
    // wraps the JITModule in `Arc<Jit>` only after `compile_to_module`
    // returns). int reads the GOT slot ptr backend wrote here + its own
    // `Arc<Jit>` to construct `Code::Jit`. (S77 re-wire.)
    //
    // Object mode: `try_get_finalized_function` returns `None` (no runtime
    // pointer before `finish()`), so the loop short-circuits without storing.
    for defn in &defns {
        let Some(&func_id) = func_ids.get(&defn.name) else {
            continue;
        };
        let Some(ptr) = module.try_get_finalized_function(func_id) else {
            // Object-mode path: no runtime pointer exists; capability is
            // module-wide, so subsequent symbols also return None.
            break;
        };

        // Resolve the entry's GOT slot and write the finalised ptr.
        let slot_opt = symbol_tables.get(&module_path).and_then(|table| {
            table
                .get(defn.name.as_ref())
                .and_then(|entry| entry.callable_got_slot())
        });
        if let Some(slot) = slot_opt {
            if let Some(table) = symbol_tables.get(&module_path) {
                table.got.store_slot(slot, ptr);
            }

            // FIXME 0099 — emit a `JitWrite` GOT event for the freshly-
            // finalised per-symbol code pointer. The consumer-side ring
            // buffer + flush-to-stderr live in `int`'s `src/got_trace/`.
            // When no observer is registered, `emit` is one relaxed-load
            // null check + branch.
            crate::got_observer::emit(
                crate::got_observer::GotEventTag::JitWrite,
                &crate::got_observer::GotEvent {
                    module: module_path.clone(),
                    symbol: defn.name.clone(),
                    slot,
                    ptr,
                    provenance: crate::got_observer::GotProvenance::Jit {
                        // Use the JITModule address as a stable correlator —
                        // `module` is a generic `M: Module`, so we cast via a
                        // raw pointer to its address for diagnostic
                        // identification only. The observer must NOT
                        // dereference.
                        jit_addr: (&*module) as *const M as *const () as usize,
                    },
                },
            );
        }
    }

    Ok(CompilationArtifacts {
        clif_ir: clif_ir_agg,
        code_size: code_size_agg,
        compile_duration: compile_start.elapsed(),
    })
}

// =========================================================================
// Free function — `load_object` (Sprint 67 Wave 3 row 3)
// =========================================================================
//
// Per `facades/backend.md` §"Free functions": the cache-hit entry point for
// reading a `.o` produced by an earlier `compile_to_object` (or `--link`)
// invocation. Wraps the existing `Linker::load_object` method shape into a
// free-function boundary so the public API matches the facade's three-entry
// shape (`compile_to_module`, `load_object`, `compile_to_object`).
//
// The free-function shape constructs a fresh `Linker`, populates it with
// the object's defined symbols, and returns a `LinkerArtefact` carrying the
// `Arc<Linker>` retention root + per-symbol address map. `int` walks the
// artefact's `ptrs` map and writes each address to the matching entry's
// GOT slot via `got().store_slot(slot, ptr)`.
//
// The full `int`-side cache-hit orchestration (registering intrinsic
// symbols, GOT base externals, etc.) does NOT live in this free function —
// callers needing the broader workflow continue to drive `Linker` directly.

/// Free-function entry point for cache-hit object loading.
///
/// Per `facades/backend.md` §"Free functions". Constructs a fresh `Linker`,
/// loads the supplied object bytes into it, and returns a `LinkerArtefact`
/// containing the `Arc<Linker>` retention root + per-symbol pointer map.
///
/// `int` walks `artefact.ptrs` and for each `(symbol, ptr)` writes the
/// ptr into the matching entry's GOT slot via `got().store_slot(slot, ptr)`
/// and stores `Code::Linker(linker.clone())` as the lifecycle owner on the
/// `ModuleEntry::Def`.
///
/// The thin wrapper here registers no externals — callers that need the
/// full cache-hit workflow (intrinsic symbol registration, GOT base
/// externals, multi-module resolution) continue to drive `cache::Linker`
/// directly. This entry exists for facade-compliance + future migration
/// of the full workflow into backend.
pub fn load_object<C, L>(
    module: &ModuleFullPath,
    object_bytes: &[u8],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Result<artefact::LinkerArtefact, CranelispError>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut linker = crate::cache::linker::Linker::new()?;
    linker.load_object(module.as_ref(), object_bytes)?;

    // Walk the module's symbol table to identify defined function symbols;
    // ask the linker for each address. Per Decision 36, the symbols are
    // stored under their bare names.
    let mut ptrs: std::collections::HashMap<Symbol, *const u8> =
        std::collections::HashMap::new();
    if let Some(st) = symbol_tables.get(module) {
        for (name, entry) in st.all_symbols() {
            if entry.callable_got_slot().is_some()
                && let Ok(addr) = linker.get_symbol(name.as_ref())
            {
                ptrs.insert(name.clone(), addr);
            }
        }
    }

    Ok(artefact::LinkerArtefact {
        linker: std::sync::Arc::new(linker),
        ptrs,
    })
}

// =========================================================================
// Free function — `produce_disasm` (S75 W2 — D41 rotation; FIXME 0221)
// =========================================================================

/// On-demand machine-code disassembly entry — the third codegen-boundary
/// free function (with `compile_to_module` + `load_object`).
///
/// Per `facades/backend.md` §"Free functions": invoked lazily by the
/// integration layer when a REPL `/disasm <fn>` request arrives, NOT eagerly
/// per-compile (disassembly is significantly more expensive than the CLIF
/// capture that `CompilationArtifacts` carries unconditionally, so it is
/// factored out of the always-created path).
///
/// Resolves `fq` to its symbol-table entry, reads the live post-compile code
/// pointer from the entry's GOT slot
/// (`symbol_table.got().load_slot(entry.got_slot.unwrap())`), reads `code_size`
/// bytes at that address, and capstone-disassembles them for the host
/// architecture.
///
/// **The caller supplies `code_size`** (S75 W2 Finding-C correction): it was
/// returned in the compile-time `CompilationArtifacts` and is passed back here.
/// Backend does NOT re-derive `code_size` — `ModuleEntry::Def` does not persist
/// it, and backend never sees int's `Introspection`. This is the on-demand
/// disassembly path (REPL `/disasm`), much more expensive than CLIF capture, so
/// factored out of the always-created `CompilationArtifacts`; production batch
/// pays nothing. Works for both the JIT path and the cache-hit path because the
/// GOT slot holds the live code address in both cases.
///
/// # Safety
///
/// Reads `code_size` bytes at the GOT-slot address via `from_raw_parts`. The
/// address is the live finalised code pointer the backend itself wrote, and the
/// caller-supplied `code_size` is the byte length the backend reported for that
/// same compilation — so the range `[ptr, ptr+code_size)` is in-bounds for the
/// finalised machine-code allocation.
pub fn produce_disasm<C, L>(
    fq: &cranelisp_types::FQSymbol,
    code_size: usize,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Result<String, CompilationError>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let table = symbol_tables.get(&fq.module).ok_or_else(|| {
        CompilationError::SymbolNotCompilable {
            module: fq.module.clone(),
            symbol: fq.symbol.clone(),
        }
    })?;
    let entry = table.get(fq.symbol.as_ref()).ok_or_else(|| {
        CompilationError::SymbolNotCompilable {
            module: fq.module.clone(),
            symbol: fq.symbol.clone(),
        }
    })?;
    let Some(slot) = entry.callable_got_slot() else {
        return Err(CompilationError::SymbolNotCompilable {
            module: fq.module.clone(),
            symbol: fq.symbol.clone(),
        });
    };
    let ptr = table.got.load_slot(slot);
    if ptr.is_null() {
        return Err(CompilationError::SymbolNotCompilable {
            module: fq.module.clone(),
            symbol: fq.symbol.clone(),
        });
    }
    if code_size == 0 {
        return Ok(String::new());
    }

    // SAFETY: see the fn-level # Safety note — `ptr` is the live finalised code
    // address backend wrote to the GOT slot; `code_size` is the byte length
    // backend reported for that compilation.
    let code_bytes: &[u8] =
        unsafe { std::slice::from_raw_parts(ptr, code_size) };
    let runtime_addr = ptr as u64;

    disasm_host(code_bytes, runtime_addr).map_err(|cause| {
        CompilationError::CodegenFailed {
            module: fq.module.clone(),
            symbol: fq.symbol.clone(),
            cause,
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    })
}

/// Disassemble `code_bytes` (at runtime virtual address `addr`) for the host
/// architecture using capstone. Returns one `0xADDR\tmnemonic operands` line
/// per instruction. The `#[cfg(target_arch)]` arms select the matching ISA;
/// architectures other than aarch64 / x86_64 return a typed error.
fn disasm_host(code_bytes: &[u8], addr: u64) -> Result<String, String> {
    use capstone::prelude::*;

    #[cfg(target_arch = "aarch64")]
    let cs = Capstone::new()
        .arm64()
        .mode(arch::arm64::ArchMode::Arm)
        .detail(false)
        .build();

    #[cfg(target_arch = "x86_64")]
    let cs = Capstone::new()
        .x86()
        .mode(arch::x86::ArchMode::Mode64)
        .detail(false)
        .build();

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let _ = (code_bytes, addr);
        return Err(
            "produce_disasm: host architecture not supported by the capstone \
             disassembler (only aarch64 and x86_64 are wired)"
                .to_string(),
        );
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        let cs = cs.map_err(|e| format!("capstone init failed: {e}"))?;
        let insns = cs
            .disasm_all(code_bytes, addr)
            .map_err(|e| format!("capstone disassembly failed: {e}"))?;
        let mut out = String::new();
        for insn in insns.iter() {
            use std::fmt::Write;
            let _ = writeln!(
                out,
                "0x{:x}\t{}\t{}",
                insn.address(),
                insn.mnemonic().unwrap_or(""),
                insn.op_str().unwrap_or(""),
            );
        }
        Ok(out)
    }
}

// =========================================================================
// Free function — `compile_trap_stub` (S101 R3 machinery, backend §8.1/§8.3)
// =========================================================================

/// Compile a per-symbol **trap stub** — the R3 redefinition machinery's
/// backend half (`design/backend/ownership-codegen.md` §8.1/§8.3; spine §5.5).
///
/// A BROKEN symbol's GOT slot is patched (by the session, via
/// `got().store_slot`) to point at this stub, so every existing unrecompiled
/// caller that dispatches through the slot raises a clean runtime error with
/// per-symbol provenance instead of executing stale code. The stub is ~5
/// instructions over the EXISTING raise machinery — `iconst msg_ptr; iconst
/// msg_len; call runtime/panic; return 0` — no new intrinsic (`runtime/panic`
/// resolves through the ordinary intrinsics registration,
/// `register_intrinsics` → `JITBuilder::symbol`).
///
/// **Signature `() -> i64`, sound for any caller arity** under the uniform
/// all-I64 value representation on both supported ABIs (SysV x86-64 /
/// AAPCS64): the stub never reads its argument registers (caller-owned
/// scratch), stack-passed args (arity > 8) are caller-cleaned in both
/// conventions, and the `0` sentinel comes back in the single return register.
/// The host surfaces the raised message via
/// `cranelisp_intrinsics::panic::take_runtime_error()` after the invocation,
/// in every mode.
///
/// Returns `(code_ptr, Code)`: the code pointer is `*const u8` — exactly what
/// `store_slot(slot, ptr)` consumes — and the `Code::Jit` handle is the
/// retention root for the stub's JIT pages (per-symbol JIT cardinality, the
/// Decision-41 norm; keep it alive for as long as the slot may be called).
///
/// # Message lifetime — the CALLER's obligation
///
/// `msg_ptr`/`msg_len` name a UTF-8, **no-NUL** provenance string
/// (`"g is broken by the redefinition of f: <original error>"`) whose ADDRESS
/// is baked into the stub as `iconst`s and read at every trap **invocation**,
/// not at compile time. The string MUST live exactly as long as the returned
/// `Code` retention handle — the session stores them paired
/// (`design/int/session-transaction.md`; `/arch` S101 Phase-2 checklist (i)).
/// The backend's obligation is only that the baked pointer is never read
/// after the `Code` handle drops.
///
/// RC-mid-panic caveat (carried, documented): a caller has already emitted
/// consuming incs for its heap args when the trap fires; the raise path
/// releases none of them — one leaked reference per trap invocation, the same
/// caveat class as every `runtime/panic` raise. Dev-session-bounded.
pub fn compile_trap_stub(
    msg_ptr: *const u8,
    msg_len: usize,
) -> Result<(*const u8, Code), CompilationError> {
    let mut jit = jit::Jit::new_with_symbols(&[]).map_err(CompilationError::from)?;
    let module = jit.jit_module();

    // `runtime/panic` via the ordinary intrinsics declaration path (no
    // bespoke symbol wiring — §8.1).
    let intrinsic_ids = declare_intrinsics_generic(module).map_err(CompilationError::from)?;
    let panic_id = intrinsic_ids.panic.unwrap_or_else(|| {
        unreachable!("invariant: runtime/panic is in the intrinsics catalog")
    });

    // Stub signature: () -> i64 (see the fn-level ABI note).
    let mut sig = module.make_signature();
    sig.returns.push(AbiParam::new(types::I64));

    let func_id = module
        .declare_function("__cranelisp_trap_stub__", cranelift_module::Linkage::Local, &sig)
        .map_err(|e| CompilationError::from(CranelispError::CodegenError {
            message: format!("failed to declare trap stub: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }))?;

    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut func_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        // Bake the provenance string's address + length; call runtime/panic
        // (stores the message in the thread-local slot and returns); return
        // the 0 sentinel.
        let ptr_val = builder.ins().iconst(types::I64, msg_ptr as i64);
        let len_val = builder.ins().iconst(types::I64, msg_len as i64);
        let panic_ref = module.declare_func_in_func(panic_id, builder.func);
        builder.ins().call(panic_ref, &[ptr_val, len_val]);
        let sentinel = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[sentinel]);
        builder.seal_all_blocks();
        builder.finalize();
    }

    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| CompilationError::from(CranelispError::CodegenError {
            message: format!("failed to define trap stub: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }))?;
    module
        .finalize_definitions()
        .map_err(|e| CompilationError::from(CranelispError::CodegenError {
            message: format!("failed to finalize trap stub: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }))?;

    let code_ptr = module.get_finalized_function(func_id);

    // Post-finalize the Jit is effectively read-only; `Code`'s
    // `unsafe impl Send + Sync` (code.rs module docs) carries the safety
    // argument. Same allow as the int-side `Arc<Jit>` construction
    // (`src/worker.rs` precedent).
    #[allow(clippy::arc_with_non_send_sync)]
    let jit_arc = std::sync::Arc::new(jit);

    Ok((code_ptr, Code::jit(jit_arc)))
}

/// Unit tests for [`compile_trap_stub`] (the R3 machinery's per-symbol trap
/// stub — backend §8.1/§8.3). Relocated from the flat crate-root `tests.rs`
/// to sit beside the code they exercise (S102 CS-B3.0, FIXME 0495; Principle
/// 23 — tests mirror module composition). Self-contained: they depend only on
/// `compile_trap_stub` + the `cranelisp-intrinsics` panic slot.
#[cfg(test)]
mod trap_stub_tests {
    use super::compile_trap_stub;

    // spec: design/backend/ownership-codegen.md §8.1 — the stub raises the baked
    // provenance message through `runtime/panic` (thread-local slot + sentinel
    // return); the host reads it via `take_runtime_error`.
    #[test]
    fn trap_stub_raises_provenance_message_and_returns_sentinel() {
        let msg = String::from("g is broken by the redefinition of f: type error");
        let (ptr, code) =
            compile_trap_stub(msg.as_ptr(), msg.len()).expect("trap stub compiles");
        assert!(!ptr.is_null(), "trap stub must finalize to a non-null code ptr");

        let _ = cranelisp_intrinsics::panic::take_runtime_error();
        let stub: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        assert_eq!(stub(), 0, "trap stub returns the 0 sentinel");
        let raised = cranelisp_intrinsics::panic::take_runtime_error()
            .expect("trap stub must raise through the runtime/panic slot");
        assert!(
            raised.contains("g is broken by the redefinition of f: type error"),
            "raised message must carry the baked provenance; got: {raised}"
        );

        // The provenance string + Code handle pair outlive the call — the
        // caller-side lifetime contract (§8.1). Keep both live to here.
        drop(code);
        drop(msg);
    }

    // spec: design/backend/ownership-codegen.md §8.1 — the `() -> i64` stub is
    // signature-safe for ANY caller arity/type vector under the uniform all-I64
    // convention: callers that imported an N-arg signature reach the same slot
    // and the stub never reads its argument registers. Pin the cross-arity call.
    #[test]
    fn trap_stub_is_callable_at_nonzero_arity() {
        let msg = String::from("h is broken by the redefinition of k: arity change");
        let (ptr, _code) =
            compile_trap_stub(msg.as_ptr(), msg.len()).expect("trap stub compiles");

        let _ = cranelisp_intrinsics::panic::take_runtime_error();
        // Call as a 3-arg function (register-passed, caller-owned scratch).
        let stub3: extern "C" fn(i64, i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
        assert_eq!(stub3(1, 2, 3), 0, "sentinel through a 3-arg import signature");
        assert!(
            cranelisp_intrinsics::panic::take_runtime_error().is_some(),
            "raise fires regardless of the caller's imported arity"
        );
    }

    // spec: design/backend/ownership-codegen.md §8.1 — the message address is
    // baked and read at INVOCATION time, so the stub is re-raisable (every call
    // through the patched slot raises afresh; the slot may be hit many times in
    // a dev session).
    #[test]
    fn trap_stub_raises_on_every_invocation() {
        let msg = String::from("m is broken by the redefinition of n: gone");
        let (ptr, _code) =
            compile_trap_stub(msg.as_ptr(), msg.len()).expect("trap stub compiles");
        let stub: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };

        for i in 0..3 {
            let _ = cranelisp_intrinsics::panic::take_runtime_error();
            assert_eq!(stub(), 0);
            assert!(
                cranelisp_intrinsics::panic::take_runtime_error().is_some(),
                "invocation {i} must raise"
            );
        }
    }
}

// NOTE: `compile_to_object` was retracted in S75 W2 (`/dev backend`) per the
// facade §"Free functions" tombstone + PIF Row 4 retraction. It was a
// Sprint-67 facade-compliance scaffold returning `unimplemented!()` and
// citing the never-filed FIXME 0184 (a dangling citation). The codegen
// boundary is the THREE free functions `compile_to_module<M>` + `load_object`
// + `produce_disasm`; the object path is `compile_to_module::<ObjectModule>`
// + caller `finish().emit()` (the §2.5 caller-finalize contract), NOT a
// separate object-compile entry.

// NOTE: `resolve_cross_module_refs` was removed in Sprint 58 Wave 2 per
// `/arch` Decision 36 + 31. Under all-GOT calling, cross-module function
// references flow through `__cranelisp_got_{other_M}`, never as direct
// `Linkage::Import` function declarations. Compile-time arity for those
// calls is resolved via `compiler::resolve_func_arity` walking the symbol
// tables.

/// Compile a single defn into a module using FnCompiler, returning the
/// per-symbol introspection artifacts captured during codegen.
#[allow(clippy::too_many_arguments)] // codegen threading: +mode_summary (B3.2)
fn compile_defn_in_module<M, C, L>(
    defn: &Defn,
    body: &cranelisp_types::MonoExpr,
    mode_summary: Option<cranelisp_types::ModeSummary>,
    module: &mut M,
    func_ctx: &mut FunctionBuilderContext,
    func_ids: &HashMap<Symbol, FuncId>,
    compile_ctx: CompileContext<'_, C, L>,
    capture_clif: bool,
) -> Result<FunctionArtifacts, CranelispError>
where
    M: Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut sig = module.make_signature();
    for _ in defn.params() {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));

    let func_id = *func_ids.get(&defn.name).ok_or_else(|| {
        CranelispError::CodegenError {
            message: format!("function '{}' not declared", defn.name),
            location: ErrorLocation::from_span(defn.span),
        }
    })?;

    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::testcase(defn.name.as_bytes()),
        sig,
    );

    FnCompiler::compile_body(defn, body, mode_summary, &mut func, func_ctx, module, compile_ctx)?;

    // Capture CLIF IR text before define_function consumes the context — but
    // only when the caller will consume it (FIXME 0325). When `capture_clif`
    // is false the `func.display()` rendering + allocation is skipped and
    // `clif_ir` stays empty; batch `--run`/`--link` with introspection off
    // drops it unread, so the work is wasted there.
    let clif_ir = if capture_clif {
        format!("{}", func.display())
    } else {
        String::new()
    };

    let mut ctx = cranelift::codegen::Context::for_function(func);
    // Disassembly is NOT captured in the always-created path (S70 Phase B
    // amendment to D41) — `produce_disasm` re-derives it on demand. Only the
    // cheap code-size byproduct is read from the compiled code.
    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define function '{}': {e}", defn.name),
            location: ErrorLocation::from_span(defn.span),
        })?;

    // Capture code size from the compiled code.
    let code_size = ctx
        .compiled_code()
        .map(|compiled| compiled.code_info().total_size)
        .unwrap_or(0);

    Ok(FunctionArtifacts {
        clif_ir,
        code_size,
    })
}


#[cfg(test)]
mod concrete_boundary_phase3_tests {
    //! S84 Phase 3 (concrete-boundary-type.md §3.1/§3.1.1, FIXME 0391): the
    //! backend consumes `MonoExpr`/`ConcreteType`. These pin the two structural
    //! seams the migration introduced — the scoped `codegen_view` backstop
    //! predicate and the signature-path `Type → ConcreteType` conversion.

    use crate::compiler::signature_heap_category;
    use crate::heap::HeapCategory;
    use cranelisp_types::{ModuleFullPath, SymbolTable, Type};

    // W0.b (`backend-keyed-consumer.md` §4 W0.b/§5) RETIRED the
    //   `requires_codegen_view` bypass: typecheck now populates a `codegen_view`
    //   for EVERY codegen-reached body (ctor/accessor synthetic bodies included),
    //   and the backend hard-errors on a `None`. The two predicate tests that
    //   pinned the "signature-driven kinds legitimately carry codegen_view: None"
    //   asymmetry were deleted with the predicate.

    // spec: concrete-boundary-type.md §3.1.1 (FIXME 0391 sites 1-3, 0394) — the
    //   signature-path heap classification. A concrete field/binding `Type`
    //   classifies via the total `ConcreteType` `classify`; a residual `Var` (a
    //   GENERIC CTOR `Def`'s own template field param — `(Some [:a val])`'s `a`)
    //   maps to `Mixed` (uniform i64 representation), restoring the pre-Phase-3
    //   generic-ctor-`Def` behaviour WITHOUT widening the `ConcreteType` classify.
    #[test]
    fn signature_path_classifies_concrete_and_var() {
        let no_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable>> = None;
        // Concrete scalars route through the total `ConcreteType` classify.
        assert_eq!(signature_heap_category(&Type::Int, no_tables), HeapCategory::NeverHeap);
        assert_eq!(signature_heap_category(&Type::String, no_tables), HeapCategory::AlwaysHeap);
        // A generic-ctor-template field `Var` → `Mixed` (uniform representation),
        // NOT a panic and NOT a widened `classify` (FIXME 0394).
        assert_eq!(signature_heap_category(&Type::Var(0), no_tables), HeapCategory::Mixed);
        assert_eq!(
            signature_heap_category(&Type::TyConApp(1, vec![Type::Int]), no_tables),
            HeapCategory::Mixed
        );
    }
}

#[cfg(test)]
mod clif_dump_tests;

// Shared harness for the relocated crate-root tests (FIXME 0495 step 1).
#[cfg(test)]
pub(crate) mod test_support;

// Relocated crate-root module-assembly + GOT-emission tests (FIXME 0495 step 1).
#[cfg(test)]
mod module_assembly_tests;
