//! `cranelisp-backend` — typed AST → Cranelift IR → executable.
//!
//! Owns codegen, reference-count (RC) emission, JIT lifecycle, caching, and
//! linking. Paired with the backend-emitted runtime library
//! (`cranelisp-primitives` and `cranelisp-intrinsics`, the D43 split of the
//! former `cranelisp-runtime`, whose intrinsics the emitted CLIF calls). This
//! crate is the only one that names Cranelift types; everything upstream of it
//! flows in through `cranelisp-types`.
//!
//! # The codegen boundary — crate-root free functions
//!
//! The crate-root codegen entries (the cache-hit loader is
//! [`cache::load_cached_object`]; `design/arch/bounded-contexts.md` §3 owns
//! what crosses the boundary):
//!
//! - [`compile_to_module`] — the sole CLIF emission path. Generic over
//!   `M: Module + CodeFinalizer`: the same body emits byte-identical CLIF
//!   whether `M` is the JIT's module from [`jit::Jit::jit_module`]
//!   (priority/REPL workers, per-symbol cardinality) or an `ObjectModule`
//!   (nice workers, per-module cardinality).
//!   **Mode is the `Module` instance the caller passes, never a parameter.**
//!   There is no separate object-compile entry — the object path is
//!   `compile_to_module::<ObjectModule>` followed by the **caller** finalising
//!   (`obj_module.finish().emit()`); see the §"Object file contract" notes in
//!   this source and the [`CodeFinalizer`] trait.
//! - [`produce_disasm`] — on-demand machine-code disassembly (REPL `/disasm`).
//!   The caller supplies `code_size` (it received it in [`CompilationArtifacts`]);
//!   backend never re-derives it. Factored out of the always-created path
//!   because disassembly is far more expensive than the CLIF capture
//!   [`CompilationArtifacts`] carries unconditionally.
//! - [`build_isa`] — the single ISA construction point (re-exported from
//!   `cache::object::build_isa`).
//!
//! `symbol_tables` (a raw `&DashMap<ModuleFullPath, SymbolTable<C, L>>`) is the
//! single source for every codegen decision — callee/GOT-target lookup, arity,
//! `entry.kind` → dispatch shape, constructor metadata, and the per-module GOT
//! layout are all read from it; there is no side channel and no mode flag.
//! **S110 W3 (`backend-keyed-consumer.md`): the backend NO LONGER resolves
//! names.** Every reference carries typecheck's `resolved_target` storage key
//! (Principle 24 "Resolve once"); codegen does ONE direct keyed fetch
//! (`CompileContext::entry_at` / `ctor_meta_at` / `got_entry_at`) and
//! kind-discriminates on the fetched entry, hard-erroring on miss — the
//! `resolve_*` resolver family (scan + import-chain walk + global fallback) was
//! deleted with this wave.
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
//! `Code::Linker` from the linker it drove through
//! [`cache::load_cached_object`]. The GOT
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
//! `compiler::apply`, discriminated off the keyed-fetched entry's
//! `DefKind::PrimitiveExtern` — `fq.symbol` IS the ABI key). Canonical:
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
//!   (transitional discriminator: the keyed-fetched entry's
//!   `callable_got_slot()`). Backend does not emit the platform GOT (the DLL
//!   exports it).
//! - **Startup-object hash baking** — [`exe::PlatformLayoutCheck`] carries the
//!   compiler-computed layout hash + platform name into int's `--link` startup
//!   emission (`int::src/exe.rs`), which bakes a `cranelisp_check_layout_hash`
//!   compare into the `start` stub; mismatch aborts at process start with
//!   rebuild guidance. (The orphaned backend startup-`.o` emitter was deleted
//!   S113 — FIXME 0635 I3; int owns the emission per BC §3 invariant 7.)
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
use cranelisp_types::{Life, Realization};
// Re-export TargetIsa for shared ISA in N-core codegen (pipeline-v3.md §6).
pub use cranelift::codegen::isa::TargetIsa;
// Re-export Cranelift module types for callers of compile_to_module.
pub use cranelift_module;
pub use cranelift_object;
pub(crate) mod compiler;
mod drop_glue;
pub mod exe;
pub mod got_observer;
pub mod heap;
pub mod jit;
pub(crate) mod primitives_inline;
mod raise;

// Platform-interface schema generator (platform-interface.md §5.5/§6.0; BC §3
// "the platform-interface codegen role"). The single generator with multiple
// callers (int's `/platform-schema` command + session-load hash check; the
// `--link` startup-object hash bake). Shares the closure-walk + substitution
// with the trace `DisplayDescriptor` baker (`compiler::trace_codegen`).
pub mod schema;

// Per-symbol lifecycle owner (Decision 35 + Decision 41). The enum's variants
// reference backend-owned `Arc<Jit>` / `Arc<Linker>`, so it lives here; the
// integration layer imports it as `cranelisp_backend::Code` to instantiate
// `SymbolTable<Code, ()>`.
pub mod code;
pub use code::Code;

// Typed error DTOs for the backend public surface: `CompilationError` is the
// typed result of `compile_to_module`; `LinkerError` is the typed result of
// `Linker::get_symbol`.
pub mod error;
pub use error::{CompilationError, LinkerError};

use std::collections::{BTreeSet, HashMap};

use cranelift_module::FuncId;

use dashmap::DashMap;

use cranelisp_types::{
    CallableTarget, ConcreteType, CranelispError, Decl, Defn, ErrorLocation, FQSymbol, JitSymbol,
    LinkerSymbol, ModuleFullPath, Span, Symbol, SymbolTable,
};

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::compiler::{CompileContext, FnCompiler};
use crate::jit::declare_intrinsics_generic;

/// One callable to compile and the modules a trace form in its body covers.
///
/// `trace_modules` is the whole covered set of a form in the target's body
/// (spec §4.12.3; `design/arch/tracing.md` §5.1.1): the module whose source
/// holds the body, the transitive closure of that module's finished reference
/// edges, and `primitives`. The backend adds no module to it, and does not ask
/// which module holds a body: listing that module is the caller's obligation.
/// A set is passed for every target, whether or not its body holds a form; an
/// empty set means a form that swaps nothing.
///
/// A form reads each listed module's table whole. When the compiled module is
/// not listed, it reads from that module's table only the instances whose
/// template module is listed. Every listed module must have a table in
/// `symbol_tables`; a missing one is a located codegen error at the form. The
/// set's contents are not otherwise checked: a module for which an image
/// holding the object defines no GOT fails at load as an unresolved
/// `__cranelisp_got_{M}`.
#[derive(Clone, Copy, Debug)]
pub struct CodegenTarget<'a> {
    target: &'a CallableTarget,
    trace_modules: &'a BTreeSet<ModuleFullPath>,
}

impl<'a> CodegenTarget<'a> {
    /// Pair `target` with the modules a trace form in its body covers.
    pub fn new(target: &'a CallableTarget, trace_modules: &'a BTreeSet<ModuleFullPath>) -> Self {
        Self {
            target,
            trace_modules,
        }
    }

    pub(crate) fn target(&self) -> &'a CallableTarget {
        self.target
    }

    pub(crate) fn trace_modules(&self) -> &'a BTreeSet<ModuleFullPath> {
        self.trace_modules
    }
}

pub(crate) fn callable_target_owner(target: &CallableTarget) -> Option<&FQSymbol> {
    match target {
        CallableTarget::Binding(owner)
        | CallableTarget::OverloadArm { owner, .. }
        | CallableTarget::MacroClause { owner, .. } => Some(owner),
        _ => None,
    }
}

pub(crate) fn callable_target_label(target: &CallableTarget) -> Option<JitSymbol> {
    match target {
        CallableTarget::Binding(owner) => Some(JitSymbol::from(owner.symbol.as_ref())),
        CallableTarget::OverloadArm { owner, arm } => Some(JitSymbol::from(format!(
            "{}$overload-arm${}",
            owner.symbol,
            arm.ordinal()
        ))),
        CallableTarget::MacroClause { owner, clause } => Some(JitSymbol::from(format!(
            "{}$macro-clause${}",
            owner.symbol,
            clause.ordinal()
        ))),
        _ => None,
    }
}

pub(crate) fn callable_arm_slot<C: cranelisp_types::CodeStore>(
    arm: &cranelisp_types::CallableArm<C>,
) -> Option<usize> {
    match &arm.life {
        Life::Concrete { slot, .. } => Some(slot.index()),
        _ => None,
    }
}

// --- CLIF dump observability (Sprint 60 Workstream B) --------------------
//
// `CRANELISP_CODEGEN_DUMP` selects which freshly-codegen'd CLIF is written
// to stderr during `compile_to_module`. This is load-bearing for diagnosing
// JIT/object divergence and codegen-layer bugs (drop glue, RC, GOT) where
// source-level reduction plateaus and only the emitted IR distinguishes
// correct vs broken output. Cache-hit paths do NOT re-codegen and so have
// nothing to dump; for those, use `/clif <name>` from the REPL, which reads
// the CLIF int retained in its introspection store.
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
    /// Canonical, module-qualified release functions emitted for concrete
    /// owning result types. Runtime addresses are present only in JIT mode.
    pub drop_glues: HashMap<ConcreteType, DropGlueArtifact>,
}

/// A canonical type-directed drop function emitted into this compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct DropGlueArtifact {
    pub symbol: LinkerSymbol,
    pub jit_address: Option<usize>,
}

/// Capability extension for the `Module` trait: post-finalize code access.
///
/// `cranelift_module::Module` does NOT expose `finalize_definitions` or
/// `get_finalized_function` — those are inherent methods on specific
/// implementations (`cranelift_jit::JITModule`) and absent from others
/// (`ObjectModule`, whose output is bytes via `finish().emit()`, not runtime
/// pointers).
///
/// Per `design/backend/compile-to-module.md` §9.1.6 and `/arch` Decision 23,
/// the JIT/Object split is a capability difference expressed on the `Module`
/// implementation — not a mode parameter on `compile_to_module`. This trait
/// provides that capability: the JIT's module ([`jit::Jit::jit_module`])
/// implements it with the real operations; `ObjectModule` implements it with
/// no-ops that surface `None` so the GOT-slot write phase stores no pointer in
/// object mode. A bare `JITModule` does not implement it, because it compiles
/// near calls (`design/backend/jit-object-convergence.md` §3).
///
/// Any new `Module` implementation that `compile_to_module` is asked to
/// target must provide an impl — either the "real" one (if it has runtime
/// code pointers) or a no-op stub (if it has no post-finalize pointer, e.g.,
/// an emitter that produces bytes).
pub trait CodeFinalizer {
    /// Finalize pending definitions so that code pointers become readable.
    /// For the JIT's module: patches relocations, makes mmap'd pages executable.
    /// For `ObjectModule`: no-op (bytes are emitted via a later `finish()`).
    ///
    /// Called once per `compile_to_module` invocation after all `define_function`
    /// calls complete. Implementations that cannot finalize (e.g., already
    /// finalized) should return an error, not silently succeed.
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError>;

    /// Read a finalized code pointer for the given `FuncId`, if this module
    /// exposes runtime pointers. Returns `None` on implementations that have
    /// no such concept (`ObjectModule`), which confines the GOT-slot write
    /// phase to JIT mode (per §9.1.6).
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
    ///   symbol is sized as `max(GOT_TABLE_SIZE, slot_count) * 8` bytes
    ///   (zero-initialized), matching the runtime `GotTable`.
    /// - `slot_funcs`: `(slot_index, FuncId)` pairs for every defined
    ///   function in this module. Each slot's 8-byte entry receives a
    ///   relocation initializer pointing to that function's local symbol.
    ///   Slots with no entry remain zero (empty slots are not currently
    ///   produced by typecheck — every defined function gets a slot).
    ///
    /// For the JIT's module: no-op. `Jit::new` binds each module's
    /// `__cranelisp_got_{M}` symbol to the runtime `SymbolTable.got.base_ptr()`
    /// in the JIT symbol lookup. The `.o` data definition is irrelevant in JIT
    /// mode (no `.o` is emitted).
    ///
    /// For `ObjectModule`: declares the symbol as a writable, 8-byte-aligned
    /// `Linkage::Export` slab of the size above, explicitly zeroed, and writes a
    /// function-address relocation at byte offset `slot_index * 8` for each
    /// `(slot_index, FuncId)` pair. The system linker (`--link` mode) and
    /// our cache `Linker` (`--run` mode after cache-hit) materialise these
    /// relocations into actual function addresses at load time.
    ///
    /// Per Decision 23: the same CLIF emitted by `compile_to_module<M>`
    /// references `__cranelisp_got_{M}` symmetrically as `Linkage::Import`
    /// in both modes; the *definition* differs by `Module` impl. JIT mode's
    /// definition lives outside `compile_to_module` (the `Jit::new` symbol
    /// binding); object mode's definition lives in this trait method, called
    /// from inside `compile_to_module`.
    fn define_module_got_data(
        &mut self,
        name: &str,
        slot_count: usize,
        slot_funcs: &[(usize, FuncId)],
    ) -> Result<(), CranelispError>;
}

impl CodeFinalizer for cranelift_object::ObjectModule {
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError> {
        // No-op: ObjectModule output is bytes via `finish().emit()`, not
        // runtime code pointers. Finalization happens at byte-emit time, not
        // here. See §9.1.6 of compile-to-module.md.
        Ok(())
    }

    fn try_get_finalized_function(&self, _func_id: FuncId) -> Option<*const u8> {
        // No runtime pointer exists for object-mode compilation. The GOT-slot
        // write phase stores nothing when this returns None.
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
                message: format!("failed to declare GOT data symbol '{name}' as Export: {e}"),
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
            let offset: u32 = (slot * 8)
                .try_into()
                .map_err(|_| CranelispError::CodegenError {
                    message: format!("GOT slot offset overflows u32 for slot {slot} in '{name}'"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
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
/// Each [`CodegenTarget`] carries the covered set of a `(trace …)` form in
/// its body; a form reads that set and no other.
///
/// Parameters derived internally:
/// - Intrinsics: declared on the module internally
/// - Bodies: each target's `Life::Concrete` arm with a `Realization::Body`;
///   the walked body is its concrete `MonoExpr` view, and the arm's `ast`
///   variant supplies only the signature (name, params, span)
/// - GOT slots: the target arm's `Life::Concrete` slot
/// - GOT base resolution: uniform — emits `global_value` against a
///   `Linkage::Import` data symbol `__cranelisp_got_{module}`; `Module`
///   implementations resolve at finalize time (linker relocations for Object;
///   `JITBuilder::symbol_lookup_fn` for JIT — caller's responsibility)
/// - Cross-module function refs: under `/arch` Decision 36 (bare-Local)
///   plus Decision 31 (all-GOT calling), every cross-module call is GOT-
///   indirect (`__cranelisp_got_{other_M}`). No `Linkage::Import` function
///   declarations are needed for cross-module fns — they are unreachable
///   by direct call. Compile-time arity for cross-module calls is read off the
///   callee's keyed-fetched entry (`CompileContext::arity_at` →
///   `param_names.len()`; S110 W3 replaced the deleted `resolve_func_arity`).
///
/// # Function naming and linkage (`/arch` Decision 36)
///
/// Every user-defined function is declared with its bare symbol-table name
/// (`defn.name`) and `Linkage::Local`, uniformly across all modules. The
/// pre-Sprint-58 `user`/`main` special case (bare-Export for those modules,
/// FQ-Export for everything else) was a defect, deleted here. Function
/// symbols never cross `.o` boundaries — every call goes through the per-
/// module GOT — so `Linkage::Local` is sufficient and avoids cross-`.o`
/// symbol-table pollution. See Decision 36 in `design/arch/AGENTS.md` and
/// `design/backend/compile-to-module.md` §7 for the full rationale.
///
/// # GOT-slot write
///
/// After every body is defined, the function calls
/// `module.finalize_for_code_read()` and — for JIT-capable modules — reads
/// each finalized code pointer and stores it into the target's GOT slot
/// (`got.store_slot(slot, ptr)`) before returning. It does not write the
/// `Code` lifecycle owner; the caller composes that. For `ObjectModule`, the
/// capability call returns `None` and no slot is written (no runtime pointer
/// exists). See §9.1 of `design/backend/compile-to-module.md`.
///
/// # GOT data symbol emission (`/arch` Decision 23 Bug B fix)
///
/// After function declarations, this function calls
/// `module.define_module_got_data(...)` to emit the per-module
/// `__cranelisp_got_{M}` data symbol. The implementation is `Module`-impl-
/// specific:
/// - the JIT's module: no-op (`Jit::new` binds this symbol to the runtime
///   `SymbolTable.got.base_ptr()`).
/// - `ObjectModule`: declares the symbol as `Linkage::Export` with a
///   zero-initialized slab of at least `GOT_TABLE_SIZE` slots and writes a
///   function-address relocation at byte offset `slot * 8` for each defined
///   function. The system linker (`--link`) and the cache `Linker` (`--run`
///   after cache-hit) resolve the relocations at load time.
pub fn compile_to_module<M, C, L>(
    module_path: ModuleFullPath,
    targets: &[CodegenTarget<'_>],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module: &mut M,
    capture_clif: bool,
) -> Result<CompilationArtifacts, CompilationError>
where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    compile_to_module_impl::<M, C, L>(
        module_path.clone(),
        targets,
        symbol_tables,
        module,
        capture_clif,
    )
    .map_err(|failure| failure.in_module(&module_path))
}

/// A failure inside `compile_to_module`, before the entry names its module.
/// A failure that names its member is already a `CompilationError`; any
/// other is the module's, `ModuleFailed` naming the compiled module
/// (`non-concrete-release-contract.md` §7.2.1, *Unattributed*).
enum EntryFailure {
    Attributed(CompilationError),
    Unattributed(CranelispError),
}

impl EntryFailure {
    fn in_module(self, module_path: &ModuleFullPath) -> CompilationError {
        match self {
            EntryFailure::Attributed(error) => error,
            EntryFailure::Unattributed(error) => error::module_failed(module_path.clone(), error),
        }
    }
}

impl From<CompilationError> for EntryFailure {
    fn from(error: CompilationError) -> Self {
        EntryFailure::Attributed(error)
    }
}

impl From<CranelispError> for EntryFailure {
    fn from(error: CranelispError) -> Self {
        EntryFailure::Unattributed(error)
    }
}

fn compile_to_module_impl<M, C, L>(
    module_path: ModuleFullPath,
    targets: &[CodegenTarget<'_>],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module: &mut M,
    capture_clif: bool,
) -> Result<CompilationArtifacts, EntryFailure>
where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let compile_start = std::time::Instant::now();
    // Derive internal dependencies.
    let intrinsic_ids = declare_intrinsics_generic(module)?;

    // Step 1 (§3.1): look up each named entry, retrieve its `MonoExpr` body +
    // ownership summary and selected-arm parameter types. The four lockstep
    // vectors + the hard `codegen_view`-
    // None producer-gap error live in `collect_compile_targets`.
    let (defns, bodies, param_types, census_frames) =
        collect_compile_targets::<C, L>(&module_path, targets, symbol_tables)?;

    // v9 ctx-vtable (`io-trampoline.md §17.3`): the S96 `inject_poll_leading_pair`
    // poll-shape operand-injection pass is DELETED. Under the ctx-vtable handle model
    // the platform poll-fn computes its token from the handle it holds and calls
    // `ctx.acquire` itself — there is no leading `(token, capacity)` pair to prepend,
    // so `compile_poll_effect` takes a poll leaf's natural args as `arg_vals[0..]`.

    if defns.is_empty() {
        return Err(CranelispError::CodegenError {
            message: "no function definitions to compile".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
        .into());
    }

    // Step 2 (§3.1): declare all functions in the module (Pass 1). Seed with the
    // intrinsic FuncIds, then the bare-name `Linkage::Local` module fns.
    let mut func_ids: HashMap<Symbol, FuncId> = intrinsic_ids.by_name.clone();
    declare_module_functions(module, &defns, &mut func_ids)?;
    let unit_slots = unit_got_slots(&module_path, symbol_tables, targets, &defns)?;

    // Declare and define result-root glue before ordinary bodies. The registry
    // inserts `Defining` entries before walking fields, so recursive and
    // mutually-recursive type graphs close through already-declared FuncIds.
    let mut glue_registry = drop_glue::DropGlueRegistry::new(
        module_path.clone(),
        intrinsic_ids
            .dealloc
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/dealloc is required for drop-glue emission".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?,
        intrinsic_ids.vec_drop,
    );
    // D6: the result-root pre-request stays a proactive superset of consumer
    // demand (ruling 9 / FIXME 0745). Only `finish()` moved — it now runs after
    // body compilation, because body compilation is where the ordinary release
    // seams request their glue (S0).
    for (defn, body) in defns.iter().zip(&bodies) {
        glue_registry
            .request_if_owning(
                module,
                symbol_tables,
                body.ty().result_root().clone(),
                defn.span,
            )
            .map_err(|error| attribute_body_codegen_error(&module_path, defn, error))?;
    }

    // No cross-module function declarations: under all-GOT calling
    // (Decision 31) cross-module calls are GOT-indirect against
    // `__cranelisp_got_{other_M}`, never direct. Compile-time arity for
    // those calls is read off the callee's keyed-fetched entry
    // (`CompileContext::arity_at`; S110 W3 replaced the deleted
    // `resolve_func_arity`) — see compiler/control_flow.rs auto-curry path.
    let func_arities: HashMap<Symbol, usize> = defns
        .iter()
        .map(|d| (d.name.clone(), d.params().len()))
        .collect();

    // Step 3 (§3.1): compile each function body (Pass 2), aggregating the
    // introspection byproducts (`clif_ir`, `code_size`).
    let (clif_ir_agg, code_size_agg) = compile_module_bodies::<M, C, L>(
        module,
        &module_path,
        symbol_tables,
        targets,
        &defns,
        &bodies,
        &param_types,
        &census_frames,
        &func_ids,
        &unit_slots,
        &func_arities,
        &intrinsic_ids,
        capture_clif,
        &mut glue_registry,
    )?;

    // S0: the completeness fence runs after body compilation and BEFORE
    // `finalize_for_code_read()`, so `project_drop_glues` still observes
    // finalized addresses (the ruling-9 artifact contract is unchanged).
    let glue_ids = glue_registry.finish()?;

    // Step 4a (§3.1): emit the per-module `__cranelisp_got_{M}` data symbol.
    emit_module_got_data::<M, C, L>(
        module,
        &module_path,
        symbol_tables,
        &defns,
        &func_ids,
        &unit_slots,
    )?;

    // Step 4: Finalize definitions.
    // For the JIT's module: patches relocations, makes code pages executable.
    // For ObjectModule: no-op (bytes emitted at a later `finish()` call).
    module.finalize_for_code_read()?;

    let drop_glues = project_drop_glues(module, glue_ids);

    // Step 5 (§3.1): per-symbol finalized-ptr → GOT-slot direct-write + GotEvent.
    write_finalized_got_slots::<M, C, L>(
        module,
        &module_path,
        symbol_tables,
        &defns,
        &func_ids,
        &unit_slots,
    );

    Ok(CompilationArtifacts {
        clif_ir: clif_ir_agg,
        code_size: code_size_agg,
        compile_duration: compile_start.elapsed(),
        drop_glues,
    })
}

fn project_drop_glues<M: CodeFinalizer>(
    module: &M,
    glue_ids: HashMap<ConcreteType, (LinkerSymbol, FuncId)>,
) -> HashMap<ConcreteType, DropGlueArtifact> {
    glue_ids
        .into_iter()
        .map(|(ty, (symbol, id))| {
            let jit_address = module.try_get_finalized_function(id).map(|p| p as usize);
            (
                ty,
                DropGlueArtifact {
                    symbol,
                    jit_address,
                },
            )
        })
        .collect()
}

/// Step 1 (S111 R5 §3.1): look up each named entry, reconstruct its single-variant
/// `Defn`, and read its `MonoExpr` body + ownership summary and parameter types
/// from the selected arm. Returns the four lockstep vectors. Owns
/// the symbol-table lookup loop AND the hard `codegen_view: None` producer-gap
/// error (§5 W0.b — no silent lenient rebuild). Pure extraction — byte-identical.
// The return is the four lockstep vectors the design (§3.1/§7) specifies;
// a named struct would be over-engineering for a single internal Step-1 helper.
#[allow(clippy::type_complexity)]
fn collect_compile_targets<C, L>(
    module_path: &ModuleFullPath,
    targets: &[CodegenTarget<'_>],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Result<
    (
        Vec<Defn>,
        Vec<cranelisp_types::MonoExpr>,
        Vec<Vec<cranelisp_types::ConcreteType>>,
        Vec<compiler::census::Frame>,
    ),
    CranelispError,
>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // Step 1: Look up each named entry and retrieve its AST body (§4 symbol-
    // table lookup loop; replaces the former `program: &Program` scan).
    // Wave 0 invariant: each entry in `names` carries `ast: Some(_)`. If not,
    // surface a codegen error naming the offending symbol — see
    // design/backend/compile-to-module.md §16.4.
    let mut defns: Vec<Defn> = Vec::with_capacity(targets.len());
    // S84 Phase 3 (concrete-boundary-type.md §3.1, FIXME 0391): the codegen walk
    // is over `MonoExpr`. For each `UserFn { Concrete{slot} }` entry the body
    // comes from the typecheck-populated `codegen_view` (every node already a
    // `ConcreteType`), NOT reconstructed from `ast`. Carried in lockstep with
    // `defns`.
    let mut bodies: Vec<cranelisp_types::MonoExpr> = Vec::with_capacity(targets.len());
    let mut param_types: Vec<Vec<cranelisp_types::ConcreteType>> =
        Vec::with_capacity(targets.len());
    let mut census_frames: Vec<compiler::census::Frame> = Vec::with_capacity(targets.len());
    {
        let table = symbol_tables
            .get(module_path)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("compile_to_module: no symbol table for module '{module_path}'"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        for target in targets.iter().map(CodegenTarget::target) {
            let Some(owner) = callable_target_owner(target) else {
                return Err(CranelispError::CodegenError {
                    message: format!("compile_to_module: unsupported target '{target:?}'"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            if owner.module != *module_path {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: target '{target:?}' belongs to module '{}', not '{module_path}'",
                        owner.module
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
            let entry =
                table
                    .get(owner.symbol.as_ref())
                    .ok_or_else(|| CranelispError::CodegenError {
                        message: format!(
                            "compile_to_module: owner '{}' not found in module '{module_path}'",
                            owner.symbol
                        ),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    })?;
            let Some(arm) = table.callable_target(target) else {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: target '{target:?}' is not an executable arm in module '{module_path}'"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            let Life::Concrete {
                realization: Realization::Body { view, .. },
                ast,
                ..
            } = &arm.life
            else {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: target '{target:?}' in module '{module_path}' is not a concrete body realization"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            let variant = ast.as_ref().ok_or_else(|| CranelispError::CodegenError {
                message: format!(
                    "compile_to_module: target '{target:?}' in module '{module_path}' has ast: None — Wave 0 invariant violated (see design/typecheck/ast-annotation.md for the categories of entries that must carry ast: Some(_))"
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
            let label =
                callable_target_label(target).ok_or_else(|| CranelispError::CodegenError {
                    message: format!("compile_to_module: unsupported target '{target:?}'"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
            let defn = Defn {
                name: Symbol::from(label.as_ref()),
                docstring: match &entry.declaration {
                    Decl::Callable(callable) => callable.docstring.clone(),
                    Decl::Overloaded(declaration) => declaration.docstring.clone(),
                    Decl::Macro(declaration) => declaration.docstring.clone(),
                    _ => None,
                },
                variants: vec![variant.clone()],
                visibility: entry.visibility,
                span: variant.span,
            };

            // The body is typecheck's codegen view, built post-mono: every node
            // carries a `ConcreteType` (concrete-boundary-type.md §3.1). A
            // codegen-reached entry without one is a producer gap, refused above.
            let body = view.body.clone();

            let census = compiler::census::Frame::of_target(
                Some(&entry.declaration),
                module_path,
                &defn.name,
            );
            // The selected arm owns the scheme. Generated overload/macro
            // labels are executable names and are not table bindings, so a
            // later lookup by `defn.name` cannot recover these types.
            let selected_param_types = compiler::defn_param_types(&defn, &arm.scheme.ty, &census)?;
            census_frames.push(census);
            defns.push(defn);
            bodies.push(body);
            param_types.push(selected_param_types);
        }
    }
    Ok((defns, bodies, param_types, census_frames))
}

/// Step 2 (S111 R5 §3.1): declare every module function with its bare
/// symbol-table name and `Linkage::Local`, mutating `func_ids` (already seeded
/// with the intrinsic FuncIds). Pure extraction — byte-identical.
///
/// Per `/arch` Decision 36: every user-defined function is declared with
/// its bare symbol-table name and `Linkage::Local`, uniformly across all
/// modules. The pre-Sprint-58 user/main vs FQ-Export discriminator is a
/// defect (see Decision 36 rationale + design/backend/compile-to-module.md
/// §7). Function symbols are intra-`.o`-only because all calls go through
/// `__cranelisp_got_{M}` (Decision 31 redefinition correctness mandates
/// GOT-indirect even for intra-module calls).
fn declare_module_functions<M: Module>(
    module: &mut M,
    defns: &[Defn],
    func_ids: &mut HashMap<Symbol, FuncId>,
) -> Result<(), CranelispError> {
    for defn in defns {
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
    Ok(())
}

/// Step 3 (S111 R5 §3.1): compile each function body (Pass 2), building the
/// per-body `CompileContext` and aggregating `(clif_ir, code_size)`. Owns the
/// once-per-invocation `CRANELISP_CODEGEN_DUMP` env read. Pure extraction —
/// byte-identical (env value is process-stable, phase order unchanged).
#[allow(clippy::too_many_arguments)]
fn compile_module_bodies<M, C, L>(
    module: &mut M,
    module_path: &ModuleFullPath,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    targets: &[CodegenTarget<'_>],
    defns: &[Defn],
    bodies: &[cranelisp_types::MonoExpr],
    param_types: &[Vec<cranelisp_types::ConcreteType>],
    census_frames: &[compiler::census::Frame],
    func_ids: &HashMap<Symbol, FuncId>,
    unit_slots: &HashMap<Symbol, usize>,
    func_arities: &HashMap<Symbol, usize>,
    intrinsic_ids: &crate::jit::IntrinsicFuncIds,
    capture_clif: bool,
    glue: &mut drop_glue::DropGlueRegistry,
) -> Result<(String, usize), CompilationError>
where
    M: Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
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

    for (index, (defn, body)) in defns.iter().zip(bodies.iter()).enumerate() {
        let compile_ctx = CompileContext {
            func_ids,
            unit_slots,
            func_arities,
            symbol_tables,
            trace_modules: targets[index].trace_modules(),
            current_module: module_path.clone(),
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc.unwrap_or_else(|| {
                unreachable!(
                    "invariant: runtime/dealloc must be declared before compile \
                     (Decision 24)"
                )
            }),
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic: intrinsic_ids.panic,
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
        let dump_this = clif_dump_matches(
            clif_dump_filter.as_deref(),
            module_path.as_ref(),
            defn.name.as_ref(),
        );
        let render_clif = capture_clif || dump_this;
        let art = compile_defn_in_module(
            defn,
            body,
            &param_types[index],
            module,
            &mut func_ctx,
            func_ids,
            compile_ctx,
            census_frames[index].clone(),
            render_clif,
            glue,
        )
        .map_err(|error| attribute_body_codegen_error(module_path, defn, error))?;
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
    Ok((clif_ir_agg, code_size_agg))
}

fn attribute_body_codegen_error(
    module_path: &ModuleFullPath,
    defn: &Defn,
    error: CranelispError,
) -> CompilationError {
    error::codegen_failed(module_path.clone(), defn.name.clone(), error)
}

fn missing_module_table(module_path: &ModuleFullPath, step: &str) -> CranelispError {
    CranelispError::CodegenError {
        message: format!("compile_to_module: no symbol table for module '{module_path}' at {step}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    }
}

/// The GOT slot each target of this unit claims, keyed by its defn name; a
/// slot-less target has none. The unit's one read of its slots: GOT data
/// emission, the finalised-pointer writes and a function value's wrapper
/// (compile-to-module §12.2) consume it, so a wrapper loads the slot that
/// receives its target's code.
fn unit_got_slots<C, L>(
    module_path: &ModuleFullPath,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    targets: &[CodegenTarget<'_>],
    defns: &[Defn],
) -> Result<HashMap<Symbol, usize>, CranelispError>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let table = symbol_tables
        .get(module_path)
        .ok_or_else(|| missing_module_table(module_path, "slot collection"))?;
    Ok(targets
        .iter()
        .map(CodegenTarget::target)
        .zip(defns)
        .filter_map(|(target, defn)| {
            let slot = table.callable_target(target).and_then(callable_arm_slot)?;
            Some((defn.name.clone(), slot))
        })
        .collect())
}

/// Step 4a (S111 R5 §3.1 / `/arch` Decision 23 Bug B fix): emit the per-module
/// GOT data symbol `__cranelisp_got_{M}`. For ObjectModule this defines a
/// `Linkage::Export` data symbol with relocation initializers against
/// each defined function's local symbol; for the JIT's module this is a no-op
/// because the JIT-mode definition lives outside `compile_to_module`.
/// See `define_module_got_data` impls and §5.4 of compile-to-module.md.
/// Pure extraction — same lock scope + drop point, byte-identical.
fn emit_module_got_data<M, C, L>(
    module: &mut M,
    module_path: &ModuleFullPath,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    defns: &[Defn],
    func_ids: &HashMap<Symbol, FuncId>,
    unit_slots: &HashMap<Symbol, usize>,
) -> Result<(), CranelispError>
where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let table = symbol_tables
        .get(module_path)
        .ok_or_else(|| missing_module_table(module_path, "GOT-data emission"))?;
    let slot_funcs: Vec<(usize, FuncId)> = defns
        .iter()
        .filter_map(|defn| Some((*unit_slots.get(&defn.name)?, *func_ids.get(&defn.name)?)))
        .collect();
    let slot_count = table
        .all_symbols()
        .filter_map(|(_, binding)| binding.callable_got_slot())
        .chain(
            table
                .codegen_targets()
                .filter_map(|(_, arm)| callable_arm_slot(arm)),
        )
        .chain(
            table
                .retired_slots()
                .iter()
                .map(|retired| retired.slot.index()),
        )
        .max()
        .map_or(0, |slot| slot + 1);
    // Drop the read guard before potentially mutating other tables.
    drop(table);

    let got_name = crate::compiler::got_data_symbol_name(module_path);
    module.define_module_got_data(&got_name, slot_count, &slot_funcs)
}

/// Step 5 (S111 R5 §3.1 / D41 #2 — per-symbol GOT slot direct-write): for each
/// compiled symbol, read its finalised code pointer and write it directly into
/// the entry's GOT slot via `symbol_table.got().store_slot(slot, ptr)` (the ONE
/// production slab write — the CS-2 GOT-backstop anchor), then emit the
/// `JitWrite` GotEvent. The GOT is the single source of truth for callable
/// addresses (Decision 35 post-rollback). Object mode:
/// `try_get_finalized_function` returns `None` (no runtime pointer before
/// `finish()`), so the loop short-circuits without storing. Pure extraction —
/// byte-identical.
///
/// The lifecycle-owner write (D41 #1 — `Code::Jit(Arc<Jit>)` via `write_code`)
/// stays in the integration layer for now: backend receives a generic `&mut M:
/// Module` and does not own the `Arc<Jit>`. int reads the GOT slot ptr backend
/// wrote here + its own `Arc<Jit>` to construct `Code::Jit`. (S77 re-wire.)
fn write_finalized_got_slots<M, C, L>(
    module: &M,
    module_path: &ModuleFullPath,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    defns: &[Defn],
    func_ids: &HashMap<Symbol, FuncId>,
    unit_slots: &HashMap<Symbol, usize>,
) where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    for defn in defns {
        let Some(&func_id) = func_ids.get(&defn.name) else {
            continue;
        };
        let Some(ptr) = module.try_get_finalized_function(func_id) else {
            // Object-mode path: no runtime pointer exists; capability is
            // module-wide, so subsequent symbols also return None.
            break;
        };

        // Write the finalised ptr into the entry's GOT slot.
        if let Some(&slot) = unit_slots.get(&defn.name) {
            if let Some(table) = symbol_tables.get(module_path) {
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
                        // Use the JIT address as a stable correlator —
                        // `module` is a generic `M: Module`, so we cast via a
                        // raw pointer to its address for diagnostic
                        // identification only. The observer must NOT
                        // dereference.
                        jit_addr: (module) as *const M as *const () as usize,
                    },
                },
            );
        }
    }
}

// =========================================================================
// Free function — `produce_disasm` (S75 W2 — D41 rotation; FIXME 0221)
// =========================================================================

/// On-demand machine-code disassembly entry.
///
/// Invoked lazily by the integration layer when a REPL `/disasm <fn>` request
/// arrives, NOT eagerly per-compile (disassembly is significantly more
/// expensive than the CLIF capture that `CompilationArtifacts` carries
/// unconditionally, so it is factored out of the always-created path).
///
/// Resolves `fq` to its symbol-table entry, reads the live post-compile code
/// pointer from the entry's GOT slot (`got.load_slot`), reads `code_size`
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
    let table =
        symbol_tables
            .get(&fq.module)
            .ok_or_else(|| CompilationError::SymbolNotCompilable {
                module: fq.module.clone(),
                symbol: fq.symbol.clone(),
            })?;
    let entry =
        table
            .get(fq.symbol.as_ref())
            .ok_or_else(|| CompilationError::SymbolNotCompilable {
                module: fq.module.clone(),
                symbol: fq.symbol.clone(),
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
    let code_bytes: &[u8] = unsafe { std::slice::from_raw_parts(ptr, code_size) };
    let runtime_addr = ptr as u64;

    disasm_host(code_bytes, runtime_addr).map_err(|cause| CompilationError::CodegenFailed {
        module: fq.module.clone(),
        symbol: fq.symbol.clone(),
        cause,
        location: ErrorLocation::from_span(Span::SYNTHETIC),
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

// NOTE: there is no object-compile entry. The object path is
// `compile_to_module::<ObjectModule>` + caller `finish().emit()`; do not
// reintroduce a separate `compile_to_object`.

// NOTE: `resolve_cross_module_refs` was removed in Sprint 58 Wave 2 per
// `/arch` Decision 36 + 31. Under all-GOT calling, cross-module function
// references flow through `__cranelisp_got_{other_M}`, never as direct
// `Linkage::Import` function declarations. Compile-time arity for those
// calls is read off the callee's keyed-fetched entry
// (`CompileContext::arity_at`; S110 W3 replaced the deleted
// `resolve_func_arity`).

/// Compile a single defn into a module using FnCompiler, returning the
/// per-symbol introspection artifacts captured during codegen.
#[allow(clippy::too_many_arguments)]
fn compile_defn_in_module<M, C, L>(
    defn: &Defn,
    body: &cranelisp_types::MonoExpr,
    param_types: &[cranelisp_types::ConcreteType],
    module: &mut M,
    func_ctx: &mut FunctionBuilderContext,
    func_ids: &HashMap<Symbol, FuncId>,
    compile_ctx: CompileContext<'_, C, L>,
    census: compiler::census::Frame,
    capture_clif: bool,
    glue: &mut drop_glue::DropGlueRegistry,
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

    let func_id = *func_ids
        .get(&defn.name)
        .ok_or_else(|| CranelispError::CodegenError {
            message: format!("function '{}' not declared", defn.name),
            location: ErrorLocation::from_span(defn.span),
        })?;

    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::testcase(defn.name.as_bytes()),
        sig,
    );

    FnCompiler::compile_body(
        defn,
        body,
        param_types,
        &mut func,
        func_ctx,
        module,
        compile_ctx,
        census,
        glue,
    )?;

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

    Ok(FunctionArtifacts { clif_ir, code_size })
}

#[cfg(test)]
mod clif_dump_tests;

// Shared harness for the relocated crate-root tests (FIXME 0495 step 1).
#[cfg(test)]
pub(crate) mod test_support;

#[cfg(test)]
pub(crate) mod test_child;

// Relocated crate-root module-assembly + GOT-emission tests (FIXME 0495 step 1).
#[cfg(test)]
mod module_assembly_tests;

#[cfg(test)]
mod macro_clause_ownership_tests;

// GOT slab-stability invariant tests, rehomed from the deleted `got.rs` shim
// (S111 R4 §1.2).
#[cfg(test)]
mod got_slab_tests;

// Standing structural fence for the "syntactic node-kind test standing in for
// the derived answer" class (S115 W4c, FIXME 0781). Cross-module by nature —
// it scans the RC-decision file set — so it lives at the crate root.
#[cfg(test)]
mod rc_ownership_fence_tests;
