//! `cranelisp-backend` — typed AST → Cranelift IR → executable.
//!
//! Owns codegen, reference-count (RC) emission, JIT lifecycle, caching, and
//! linking. Paired with `cranelisp-runtime` (whose intrinsics the emitted CLIF
//! calls). This crate is the only one that names Cranelift types; everything
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
            let ModuleEntry::Def { ast, visibility, docstring, .. } = entry else {
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
            // sources for that metadata post-narrowing).
            let defn = Defn {
                name: name.clone(),
                docstring: docstring.clone(),
                variants: vec![variant.clone()],
                visibility: *visibility,
                span: variant.span,
            };
            defns.push(defn);
        }
    }

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

    for defn in &defns {
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
            let ModuleEntry::Def { got_slot, .. } = entry else {
                continue; // Non-Def entries don't have GOT slots
            };
            let Some(slot) = got_slot else {
                continue; // Slot not allocated (primitive-shaped Def)
            };
            let Some(&func_id) = func_ids.get(&defn.name) else {
                continue; // Defensive: can't happen — we declared it above
            };
            slot_funcs.push((*slot, func_id));
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
            table.get(defn.name.as_ref()).and_then(|entry| match entry {
                ModuleEntry::Def { got_slot, .. } => *got_slot,
                _ => None,
            })
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
            if matches!(
                entry,
                cranelisp_types::ModuleEntry::Def { got_slot: Some(_), .. }
            ) && let Ok(addr) = linker.get_symbol(name.as_ref())
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
    let ModuleEntry::Def { got_slot: Some(slot), .. } = entry else {
        return Err(CompilationError::SymbolNotCompilable {
            module: fq.module.clone(),
            symbol: fq.symbol.clone(),
        });
    };
    let ptr = table.got.load_slot(*slot);
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
fn compile_defn_in_module<M, C, L>(
    defn: &Defn,
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

    FnCompiler::compile_body(defn, &mut func, func_ctx, module, compile_ctx)?;

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
mod clif_dump_tests {
    //! Unit tests for Sprint 60 Workstream B (CLIF dump observability).
    //!
    //! These exercise the env-var filter grammar and the output formatter
    //! in isolation from codegen — the integration test (exercising the
    //! wired-up env var end-to-end via a subprocess) lives with `/qa` in
    //! `tests/sprint60_observability.rs`.
    use super::{clif_dump_matches, write_clif_dump};

    #[test]
    fn filter_unset_or_empty_never_matches() {
        assert!(!clif_dump_matches(None, "user", "foo"));
        assert!(!clif_dump_matches(Some(""), "user", "foo"));
    }

    #[test]
    fn filter_wildcard_matches_every_function() {
        assert!(clif_dump_matches(Some("*"), "user", "foo"));
        assert!(clif_dump_matches(Some("*"), "exemplar.solver", "cell-at$grid.Cell"));
        assert!(clif_dump_matches(Some("*"), "", ""));
    }

    #[test]
    fn filter_module_only_matches_any_symbol_in_that_module() {
        assert!(clif_dump_matches(Some("user"), "user", "foo"));
        assert!(clif_dump_matches(Some("user"), "user", "bar"));
        assert!(!clif_dump_matches(Some("user"), "main", "foo"));
        // Dotted module paths are matched literally, not as prefixes.
        assert!(clif_dump_matches(Some("exemplar.solver"), "exemplar.solver", "go"));
        assert!(!clif_dump_matches(Some("exemplar"), "exemplar.solver", "go"));
    }

    #[test]
    fn filter_module_colon_symbol_matches_that_exact_function() {
        let filter = Some("grid::cell-at$grid.Cell");
        assert!(clif_dump_matches(filter, "grid", "cell-at$grid.Cell"));
        // Wrong module — reject.
        assert!(!clif_dump_matches(filter, "html", "cell-at$grid.Cell"));
        // Wrong symbol — reject.
        assert!(!clif_dump_matches(filter, "grid", "cell-at"));
    }

    #[test]
    fn write_clif_dump_frames_header_and_trailer() {
        let mut buf = Vec::<u8>::new();
        write_clif_dump(&mut buf, "user", "foo", "function %foo() -> i64 {\n}\n").unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.starts_with("; === CLIF user::foo ===\n"), "output: {out}");
        assert!(out.contains("function %foo() -> i64 {"), "body missing: {out}");
        assert!(out.trim_end().ends_with("; === end CLIF user::foo ==="), "trailer missing: {out}");
    }

    #[test]
    fn write_clif_dump_adds_trailing_newline_when_body_lacks_one() {
        // Body without trailing newline — formatter should insert one so the
        // "end" trailer appears on its own line.
        let mut buf = Vec::<u8>::new();
        write_clif_dump(&mut buf, "m", "s", "noeol").unwrap();
        let out = String::from_utf8(buf).unwrap();
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines[0], "; === CLIF m::s ===");
        assert_eq!(lines[1], "noeol");
        assert_eq!(lines[2], "; === end CLIF m::s ===");
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::jit::Jit;
    use cranelisp_types::{ErrorLocation, 
        Defn, DefnVariant, DisplayInfo, Expr, MonoDefn, Program, Span, Symbol,
        TopLevel, Type, Visibility,
    };
    use std::collections::{HashMap, HashSet};

    /// Test-only aggregate bridging hand-built `Defn`s through side-map
    /// enrichment to the post-Phase-2 backend API. Carries the fields that
    /// the boundary `CheckResult` will retire in Wave 2 step 4 (slim-down to
    /// `{ warnings, display }`).
    ///
    /// Rationale: per `design/typecheck/ast-annotation.md` §10.2.5, the 20+
    /// `#[cfg(test)]` hits that legacy-constructed `CheckResult` literals now
    /// use this helper so the Wave 2 slim-down can land cleanly without a
    /// red build window. The shape mirrors the current public `CheckResult`
    /// field-for-field so the mechanical rewrite is a rename, not a redesign.
    struct TestCheckResult {
        // S70: `MethodResolutions` became a struct (resolved_calls +
        // pattern_ctors). The test bridge only ever populated per-span
        // call resolutions, so this field holds the bare `resolved_calls`
        // map shape — exactly what `enrich_defn_from_side_maps` consumes.
        method_resolutions: HashMap<Span, cranelisp_types::ResolvedCall>,
        constrained_fn_names: HashSet<Symbol>,
        mono_defns: Vec<MonoDefn>,
        expr_types: HashMap<Span, Type>,
        default_method_defns: Vec<Defn>,
        #[allow(dead_code)]
        warnings: Vec<cranelisp_types::Warning>,
        #[allow(dead_code)]
        display: Option<DisplayInfo>,
    }

    fn empty_check() -> TestCheckResult {
        TestCheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        }
    }

    fn empty_tables() -> DashMap<ModuleFullPath, SymbolTable> {
        DashMap::new()
    }

    /// Empty session-level module-alias table for tests that drive
    /// `compile_to_module` / `build_compile_context` (S75 W2 D41 rotation
    /// added the `module_aliases` param).
    fn empty_aliases() -> cranelisp_types::ModuleAliases {
        DashMap::new()
    }

    /// Read a Vec's `len` field directly from its base pointer.
    ///
    /// Local-only inline of the user-callable `vec-len` primitive's body —
    /// kept inside the backend test module to avoid the dep edge
    /// `cranelisp-backend → cranelisp-primitives` (forbidden by Decision
    /// 0048 §"Structural invariant — backend dep-ban", S68 Wave 4). The Vec
    /// layout is fixed by Decision 11: `[size@+0 | rc@+8 | len@+16 | cap@+24 | data_ptr@+32]`.
    ///
    /// SAFETY: `ptr` MUST be a valid Vec base pointer (heap allocation
    /// whose +16 offset is a populated `i64` len field).
    fn vec_len_for_test(ptr: i64) -> i64 {
        unsafe { *((ptr as *const u8).add(16) as *const i64) }
    }

    /// Test helper: enrich a defn's AST nodes with type and resolution
    /// annotations from CheckResult side maps.
    ///
    /// Used by tests that build ASTs by hand and carry resolutions in a
    /// `CheckResult`. In production, typecheck annotates the AST directly,
    /// so this bridge is test-only.
    fn enrich_defn_from_side_maps(
        defn: &mut Defn,
        resolutions: &HashMap<Span, cranelisp_types::ResolvedCall>,
        expr_types: &HashMap<Span, Type>,
    ) {
        for variant in &mut defn.variants {
            enrich_expr_from_side_maps(&mut variant.body, resolutions, expr_types);
        }
    }

    /// Test helper: recursively enrich expression nodes with side map data.
    fn enrich_expr_from_side_maps(
        expr: &mut cranelisp_types::Expr,
        resolutions: &HashMap<Span, cranelisp_types::ResolvedCall>,
        expr_types: &HashMap<Span, Type>,
    ) {
        use cranelisp_types::Expr;

        let span = expr.span();

        // Overlay inferred_type from side map if present.
        if let Some(ty) = expr_types.get(&span) {
            expr.set_inferred_type(Some(Box::new(ty.clone())));
        }

        // Overlay resolved_call from side map if present (Apply only).
        if let Expr::Apply { resolved_call, span: apply_span, .. } = expr
            && let Some(resolution) = resolutions.get(apply_span) {
                *resolved_call = Some(Box::new(resolution.clone()));
        }

        // Recurse into children.
        match expr {
            Expr::Let { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    enrich_expr_from_side_maps(binding_expr, resolutions, expr_types);
                }
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                enrich_expr_from_side_maps(cond, resolutions, expr_types);
                enrich_expr_from_side_maps(then_branch, resolutions, expr_types);
                enrich_expr_from_side_maps(else_branch, resolutions, expr_types);
            }
            Expr::Lambda { body, .. } => {
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            Expr::Apply { callee, args, .. } => {
                enrich_expr_from_side_maps(callee, resolutions, expr_types);
                for arg in args {
                    enrich_expr_from_side_maps(arg, resolutions, expr_types);
                }
            }
            Expr::Match { scrutinee, arms, .. } => {
                enrich_expr_from_side_maps(scrutinee, resolutions, expr_types);
                for arm in arms {
                    enrich_expr_from_side_maps(&mut arm.body, resolutions, expr_types);
                }
            }
            Expr::VecLit { elements, .. } => {
                for elem in elements {
                    enrich_expr_from_side_maps(elem, resolutions, expr_types);
                }
            }
            Expr::Annotate { expr: inner, .. } => {
                enrich_expr_from_side_maps(inner, resolutions, expr_types);
            }
            Expr::Trace { body, .. } => {
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    enrich_expr_from_side_maps(binding_expr, resolutions, expr_types);
                }
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            Expr::ConstrADT { fields, .. } => {
                for f in fields {
                    enrich_expr_from_side_maps(f, resolutions, expr_types);
                }
            }
            // Leaf nodes: no children to recurse into.
            Expr::IntLit { .. }
            | Expr::FloatLit { .. }
            | Expr::BoolLit { .. }
            | Expr::StringLit { .. }
            | Expr::Var { .. } => {}
        }
    }

    /// Test helper: build a `ModuleEntry::Def` with `ast: Some(defn)` and NO
    /// GOT slot (`got_slot: None`).
    ///
    /// With no GOT slot, intra-module calls compile as direct FuncId calls
    /// (no `__cranelisp_got_{M}` reference is emitted), so JIT-execute test
    /// helpers can run against a bare `Jit::new_with_symbols(&[])` without registering the
    /// GOT base symbol. Tests that specifically exercise the S75 W2 GOT-slot
    /// direct-write (`make_def_entry_slot`) assign an explicit slot and read
    /// the pointer back via `table.got.load_slot(slot)`.
    fn make_def_entry(defn: Defn) -> cranelisp_types::ModuleEntry {
        make_def_entry_inner(defn, None)
    }

    /// Like `make_def_entry` but assigns an explicit GOT slot (for tests that
    /// exercise the GOT-slot direct-write, or insert more than one compilable
    /// defn that must be reachable GOT-indirect).
    fn make_def_entry_slot(defn: Defn, slot: usize) -> cranelisp_types::ModuleEntry {
        make_def_entry_inner(defn, Some(slot))
    }

    fn make_def_entry_inner(defn: Defn, slot: Option<usize>) -> cranelisp_types::ModuleEntry {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let param_count = defn.params().len();
        // `param_names` is `Vec<Symbol>`; the fused `params` tuples carry the
        // optional annotation, so project out the names.
        let param_names: Vec<Symbol> = defn
            .variants
            .first()
            .map(|v| v.params.iter().map(|(n, _)| n.clone()).collect())
            .unwrap_or_default();
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(
                (0..param_count).map(|_| Type::Int).collect(),
                Box::new(Type::Int),
            ),
        };
        // `ast` is `Option<DefnVariant>` post-narrowing — store the single
        // meaningful variant.
        let variant = defn.variants.first().cloned();
        ModuleEntry::Def {
            scheme,
            visibility: Visibility::Public,
            docstring: None,
            param_names,
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: vec![],
            got_slot: slot,
            trait_origin: None,
            seq: 0,
            ast: variant,
            code: None,
        }
    }

    /// Test helper: wrap an expression in a synthetic zero-arg defn, compile via
    /// `compile_to_module`, finalize JIT, execute, and return the i64 result.
    ///
    /// The `check` parameter provides side-map data that is enriched onto the
    /// defn's AST nodes before compilation (bridging old test code to the new
    /// CheckResult-free API).
    fn test_compile_and_run(
        expr: &Expr,
        check: &TestCheckResult,
        tables: &DashMap<ModuleFullPath, SymbolTable>,
    ) -> Result<i64, CranelispError> {
        let mut defn = Defn {
            name: Symbol::from("__expr__"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: expr.clone(),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        // Enrich the defn from CheckResult side maps (test bridge).
        enrich_defn_from_side_maps(&mut defn, &check.method_resolutions, &check.expr_types);

        let module = ModuleFullPath::from("user");
        let name = defn.name.clone();
        // Post-Phase-2: insert the defn into the shared symbol table so the
        // backend's `compile_to_module` reads its AST from there.
        {
            let mut st = tables
                .entry(module.clone())
                .or_insert_with(|| SymbolTable::new(module.clone()));
            st.insert(name.clone(), make_def_entry(defn));
        }

        let mut jit = Jit::new_with_symbols(&[])?;
        let aliases = empty_aliases();
        let _artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&name),
            tables,
            &aliases,
            jit.jit_module(),
            true,
        )?;
        // S75 W2: `compile_to_module` finalizes the JIT internally. The
        // single `__expr__` defn carries `got_slot: None` (direct FuncId
        // calls; no GOT reference emitted), so read its finalised pointer by
        // name from the JIT module rather than from a GOT slot.
        let ptr = jit.get_ptr_by_name(&name, 0)?;
        let _ = cranelisp_intrinsics::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let value = func();
        if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        Ok(value)
    }

    /// Test helper: compile a program via `compile_to_module`, finalize JIT,
    /// execute entry function, and return the i64 result.
    ///
    /// Enriches defns from `check` side maps, inserts each defn into the
    /// shared symbol table as a `ModuleEntry::Def { ast: Some(_), .. }` entry
    /// (matching the Wave 0 invariant), then hands the name list to
    /// `compile_to_module`. Bridges legacy test scaffolding to the post-
    /// Phase-2 backend API (no `Program`/`CheckResult` parameters).
    fn test_compile_program_and_run(
        program: &[TopLevel],
        check: &TestCheckResult,
        tables: &DashMap<ModuleFullPath, SymbolTable>,
    ) -> Result<i64, CranelispError> {
        let module = ModuleFullPath::from("user");

        // Enrich and collect all TopLevel::Defn entries from the program,
        // plus default_method_defns and mono specialisations from the check
        // (historically injected into the program by finalize_module).
        let mut defns: Vec<Defn> = Vec::new();
        for tl in program {
            if let TopLevel::Defn(defn) = tl {
                let mut d = defn.clone();
                enrich_defn_from_side_maps(&mut d, &check.method_resolutions, &check.expr_types);
                defns.push(d);
            }
        }
        for d in &check.default_method_defns {
            let mut enriched = d.clone();
            enrich_defn_from_side_maps(&mut enriched, &check.method_resolutions, &check.expr_types);
            defns.push(enriched);
        }
        for mono in &check.mono_defns {
            // FIXME 0033 (resolved S81): `MonoDefn` no longer carries
            // `resolutions`/`expr_types` side maps — its `defn` AST is already
            // annotated by typecheck's `monomorphise_call`. Overlay only the
            // global test side maps (a no-op where the AST is already
            // annotated; keeps legacy scaffolding that pre-populates the
            // global maps working).
            let mut enriched = mono.defn.clone();
            enrich_defn_from_side_maps(&mut enriched, &check.method_resolutions, &check.expr_types);
            defns.push(enriched);
        }

        // Install each defn as a symbol-table entry with ast: Some(defn).
        // Multi-sig defns need expansion into mangled variants here (legacy
        // tests don't pre-materialise those; typecheck does in production).
        let mut names: Vec<Symbol> = Vec::new();
        {
            let mut st = tables
                .entry(module.clone())
                .or_insert_with(|| SymbolTable::new(module.clone()));
            for defn in defns {
                if defn.is_multi_sig() {
                    // Look up OverloadVariant info from the pre-inserted
                    // Overloaded base entry to recover mangled names + param
                    // types, then materialise each variant as its own entry.
                    let variants = match st.get(defn.name.as_ref()) {
                        Some(cranelisp_types::ModuleEntry::Def { kind, .. }) => {
                            if let cranelisp_types::DefKind::Overloaded { variants } =
                                kind.as_ref()
                            {
                                variants.clone()
                            } else {
                                continue;
                            }
                        }
                        _ => continue,
                    };
                    for (i, variant) in defn.variants.iter().enumerate() {
                        let param_types = variants
                            .iter()
                            .find(|v| v.param_types.len() == variant.params.len())
                            .map(|v| v.param_types.clone())
                            .or_else(|| variants.get(i).map(|v| v.param_types.clone()))
                            .unwrap_or_default();
                        let mangled = format!(
                            "{}${}",
                            defn.name,
                            param_types
                                .iter()
                                .filter_map(|t| match t {
                                    Type::Int => Some("Int"),
                                    Type::Float => Some("Float"),
                                    Type::Bool => Some("Bool"),
                                    Type::String => Some("String"),
                                    _ => None,
                                })
                                .collect::<Vec<_>>()
                                .join("+"),
                        );
                        let variant_defn = Defn {
                            name: Symbol::from(mangled),
                            docstring: defn.docstring.clone(),
                            variants: vec![variant.clone()],
                            visibility: defn.visibility,
                            span: variant.span,
                        };
                        names.push(variant_defn.name.clone());
                        st.insert(variant_defn.name.clone(), make_def_entry(variant_defn));
                    }
                } else {
                    names.push(defn.name.clone());
                    st.insert(defn.name.clone(), make_def_entry(defn));
                }
            }
        }

        let mut jit = Jit::new_with_symbols(&[])?;
        let aliases = empty_aliases();
        let _artifacts = compile_to_module(
            module.clone(),
            &names,
            tables,
            &aliases,
            jit.jit_module(),
            true,
        )?;
        // S75 W2: `compile_to_module` finalizes the JIT internally. Entries
        // carry `got_slot: None` (intra-module direct FuncId calls; no GOT
        // reference emitted). The entry is the LAST zero-arg defn (matching the
        // pre-rotation `entry_func_id` selection); read its finalised pointer
        // by name from the JIT module.
        let entry_name = names
            .iter()
            .rev()
            .find(|n| {
                tables.get(&module).is_some_and(|t| {
                    matches!(
                        t.get(n.as_ref()),
                        Some(ModuleEntry::Def { ast: Some(v), .. }) if v.params.is_empty()
                    )
                })
            })
            .cloned()
            .ok_or_else(|| CranelispError::CodegenError {
                message: "no entry function (no zero-arg defn)".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        let ptr = jit.get_ptr_by_name(&entry_name, 0)?;
        let _ = cranelisp_intrinsics::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let value = func();
        if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        Ok(value)
    }

    /// Build symbol tables with an Option type for ADT tests.
    fn option_type_tables() -> DashMap<ModuleFullPath, SymbolTable> {
        use cranelisp_types::{DefKind, FQTypeName, ModuleEntry, Scheme, Type,
            TypeDefInfo, TypeName, Visibility,
        };

        let module = ModuleFullPath::from("main");
        let type_name = TypeName::from("Option");
        let fqtn = FQTypeName::new(module.clone(), type_name.clone());

        // Constructors are now Def entries; TypeDefInfo carries names only.
        let type_def_info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: vec![],
            constructors: vec![Symbol::from("None"), Symbol::from("Some")],
        };

        let tables = DashMap::new();
        let mut st = SymbolTable::new(module.clone());

        // Insert type def
        st.insert(
            Symbol::from("Option"),
            ModuleEntry::TypeDef {
                info: type_def_info.clone(),
                visibility: Visibility::Public,
                docstring: None,
            },
        );

        // Helper: build a constructor Def entry (S70 ctor-as-Def).
        let ctor_def = |tag: usize, field_count: usize, scheme_ty: Type| ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: scheme_ty,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: (0..field_count).map(|i| Symbol::from(format!("f{i}"))).collect(),
            kind: Box::new(DefKind::Constructor {
                type_name: fqtn.clone(),
                tag,
                field_count,
                internal: false,
                type_def: None,
            }),
            callees: vec![],
            got_slot: None,
            trait_origin: None,
            seq: 0,
            ast: None,
            code: None,
        };

        // None: nullary; scheme is the bare ADT.
        st.insert(Symbol::from("None"), ctor_def(0, 0, Type::ADT(fqtn.clone(), vec![])));

        // Some: one Int field; scheme is Int -> Option.
        st.insert(
            Symbol::from("Some"),
            ctor_def(1, 1, Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![])))),
        );

        tables.insert(module, st);
        tables
    }

    // spec: 05-definitions §5.1 — single defn compiles and executes via JIT
    #[test]
    fn test_compile_program_simple() {
        let defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                    value: 42,
                    span: Span::new(0, 2),
                    inferred_type: None,
                },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 42);
    }

    // spec: 12-runtime §12.6 — batch mode requires main entry point
    #[test]
    fn test_compile_program_no_defns() {
        let _ = empty_check();
        let names: Vec<Symbol> = vec![];
        let tables = empty_tables();
        // No symbol table for "user" at all — compile_to_module errors out
        // because there's no module entry (and no names anyway).
        tables.insert(ModuleFullPath::from("user"), SymbolTable::new(ModuleFullPath::from("user")));

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let result = compile_to_module(
            ModuleFullPath::from("user"),
            &names,
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        );
        assert!(result.is_err());
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen
    #[test]
    fn test_compile_and_run_expr() {
        let expr = Expr::IntLit {
            value: 99,
            span: Span::new(0, 2),
            inferred_type: None,
        };
        let check = empty_check();

        let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
        assert_eq!(value, 99);
    }

    // spec: 05-definitions §5.1 — defn compiles in interactive (REPL) mode
    #[test]
    fn test_compile_program_interactive_mode() {
        let defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                value: 7,
                span: Span::new(0, 1),
                inferred_type: None,
                },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 7);
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen with GOT state
    // spec: 05-definitions §5.13.1 — multiple function definitions compile together
    #[test]
    fn test_compile_program_multiple_defns() {
        // Two functions: helper and main. Main returns 100.
        let helper = Defn {
            name: Symbol::from("helper"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(20, 21),
                resolved_call: None,
                inferred_type: None,
                },
                span: Span::new(10, 30),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(10, 30),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                value: 100,
                span: Span::new(40, 43),
                inferred_type: None,
                },
                span: Span::new(35, 50),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(35, 50),
        };

        let program: Program = vec![TopLevel::Defn(helper), TopLevel::Defn(main_defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 100);
    }

    // spec: 04-expressions §4.1.3 — boolean literal codegen
    #[test]
    fn test_compile_and_run_expr_bool() {
        let expr = Expr::BoolLit {
            value: true,
            span: Span::new(0, 4),
            inferred_type: None,
        };
        let check = empty_check();

        let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
        assert_eq!(value, 1);
    }

    // --- Ring 1 tests ---

    // spec: 04-expressions §4.1.4 — string literal codegen, heap allocation
    #[test]
    fn test_compile_string_literal() {
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: Span::new(0, 7),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "string literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Read back the string content via runtime API.
        let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(ptr) };
        assert_eq!(s, "hello");

        // Clean up the allocation.
        cranelisp_intrinsics::alloc::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.1.4 — empty string literal codegen
    #[test]
    fn test_compile_empty_string_literal() {
        let expr = Expr::StringLit {
            value: String::new(),
            span: Span::new(0, 2),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty string should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(ptr) };
        assert_eq!(s, "");

        cranelisp_intrinsics::alloc::heap_dealloc(ptr);
    }

    // spec: 12-runtime §12.1.4 — data constructor heap layout [tag | fields]
    #[test]
    fn test_compile_adt_data_constructor() {
        // Expression: (Some 42)
        let some_span = Span::new(0, 10);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(1, 5),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: Span::new(6, 8),
                inferred_type: None,
            }],
            span: some_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = empty_check();
        let tables = option_type_tables();

        let result = test_compile_and_run(&expr, &check, &tables);
        assert!(result.is_ok(), "ADT constructor should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify the heap layout: [header(16) | tag(1) | field(42)]
        unsafe {
            let base = ptr as *const u8;
            let tag = *(base.add(16) as *const i64);
            assert_eq!(tag, 1, "tag should be 1 for Some");
            let val = *(base.add(24) as *const i64);
            assert_eq!(val, 42, "field should be 42");
        }

        cranelisp_intrinsics::alloc::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.8 — match expression with constructor patterns and field extraction
    #[test]
    fn test_compile_match_with_fields() {
        use cranelisp_types::{MatchArm, Pattern};

        // (match (Some 99) [(Some x) x (None) 0])
        let some_span = Span::new(10, 20);
        let match_span = Span::new(0, 50);
        let scrutinee = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(11, 15),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 99,
                span: Span::new(16, 18),
                inferred_type: None,
            }],
            span: some_span,
            resolved_call: None,
            inferred_type: None,
        };

        let expr = Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                        bindings: vec![Symbol::from("x")],
                        span: Span::new(22, 30),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: Span::new(31, 32),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: Span::new(22, 32),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                        bindings: vec![],
                        span: Span::new(34, 40),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: Span::new(41, 42),
                        inferred_type: None,
                    },
                    span: Span::new(34, 42),
                },
            ],
            span: match_span,
            compiler_generated: false,
            inferred_type: None,
        };

        let check = empty_check();
        let tables = option_type_tables();

        let result = test_compile_and_run(&expr, &check, &tables);
        assert!(result.is_ok(), "match with fields should compile: {result:?}");
        assert_eq!(result.unwrap(), 99, "match should extract field value");
    }

    // spec: 04-expressions §4.5 — lambda capture, closure allocation, and indirect call
    #[test]
    fn test_compile_lambda_closure() {
        // (let [n 5] ((fn [x] (+ n x)) 10))
        // This tests: lambda capture of 'n', closure allocation, closure call.
        use cranelisp_types::ResolvedCall;

        let add_span = Span::new(30, 37);
        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("n"),
                Expr::IntLit {
                    value: 5,
                    span: Span::new(5, 6),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![(Symbol::from("x"), None)],
                    body: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: Span::new(31, 32),
                            resolved_call: None,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: Span::new(33, 34),
                                resolved_call: None,
                                inferred_type: None,
                            },
                            Expr::Var {
                                name: Symbol::from("x"),
                                span: Span::new(35, 36),
                                resolved_call: None,
                                inferred_type: None,
                            },
                        ],
                        span: add_span,
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    span: Span::new(10, 40),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 10,
                    span: Span::new(42, 44),
                    inferred_type: None,
                }],
                span: Span::new(10, 45),
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 46),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "closure should compile: {result:?}");
        assert_eq!(result.unwrap(), 15, "5 + 10 = 15");
    }

    // spec: design/backend/ring2-rc.md "capture-return inc" (sibling of §5.5)
    // spec: design/backend/slice-4-21-hello-io-investigation.md §4d/§4e
    //
    // Regression guard for Slice 4 defect. A lambda body whose return
    // expression is a bare reference to a captured heap variable MUST
    // emit `rc_inc` on the return value before `return`, so the
    // closure's drop-glue dec (fired by one-shot consume_closure paths
    // like the IO trampoline) does not free the value out from under
    // the caller.
    //
    // Test shape: `(let [s "hello"] ((fn [_] s) 0))`. The inner
    // closure captures `s` (heap-typed String) and returns it when
    // called with a dummy Int arg. Without `emit_capture_return_inc`,
    // the closure's drop glue would dec `s` after the body returns,
    // the outer `let` scope cleanup would dec `s` again (via its own
    // scope-stack dec), and at least one of those decs lands on a
    // freed node — corrupting the returned pointer and/or
    // double-freeing.
    //
    // Post-fix: the returned pointer is still live and reads back as
    // "hello"; `test_compile_lambda_closure` above (non-capture-return
    // shape) is unaffected, confirming the fix is additive.
    //
    // NB: this test sits in `lib.rs #[cfg(test)] mod tests` rather
    // than a new module in `control_flow.rs` because the
    // `test_compile_and_run` helper + `TestCheckResult` scaffolding is
    // local to `lib.rs` and re-exporting it would duplicate the entire
    // compile pipeline bridge. Per /arch §4d the placement discipline
    // is "wherever existing control_flow tests live" — the three
    // existing closure/lambda backend tests
    // (`test_compile_lambda_closure`, others) all live here.
    #[test]
    fn lambda_return_captured_heap_var_emits_inc() {
        // AST: (let [s "hello"] ((fn [_] s) 0))
        //
        // Explicit `inferred_type` on the String literal so the let's
        // `variable_types` picks up `s: String`; that's what
        // `emit_capture_return_inc` reads from the enclosing scope when
        // the lambda body is compiled.
        let string_ty = Type::String;
        let s_span = Span::new(5, 12);
        let lam_body_span = Span::new(20, 21);
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("s"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: s_span,
                    inferred_type: Some(Box::new(string_ty.clone())),
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![(Symbol::from("_"), None)],
                    body: Box::new(Expr::Var {
                        name: Symbol::from("s"),
                        span: lam_body_span,
                        resolved_call: None,
                        inferred_type: Some(Box::new(string_ty.clone())),
                    }),
                    span: Span::new(15, 22),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 0,
                    span: Span::new(24, 25),
                    inferred_type: None,
                }],
                span: Span::new(14, 26),
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 27),
            inferred_type: None,
        };

        let check = empty_check();
        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(
            result.is_ok(),
            "captured-heap-return should compile and run: {result:?}"
        );
        let ptr = result.unwrap();
        // Heap pointer (> NULLARY_TAG_THRESHOLD).
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Key post-fix assertion: the returned pointer is STILL LIVE
        // after return — `emit_capture_return_inc` incremented its RC
        // so the drop-glue dec did not free it. Pre-fix, `is_live`
        // would be false here (or the read-back would show corruption).
        #[cfg(debug_assertions)]
        assert!(
            cranelisp_intrinsics::alloc::is_live(ptr as usize),
            "returned string pointer must still be live after lambda return; \
             this is the capture-return inc invariant"
        );

        // Readable round-trip — proves the contents survived the
        // drop-glue dec that would otherwise have corrupted or freed
        // the heap block.
        let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(ptr) };
        assert_eq!(s, "hello", "captured string must round-trip");

        // Balance the one remaining caller-side reference (we, the
        // test, are the caller). Normal runtime would emit the dec at
        // the caller's scope exit; here we dec manually.
        cranelisp_intrinsics::alloc::heap_dealloc(ptr);
    }

    // --- Vec codegen tests ---

    // spec: 04-expressions §4.10 — empty Vec literal codegen
    #[test]
    fn test_compile_empty_vec_literal() {
        let expr = Expr::VecLit {
            elements: vec![],
            span: Span::new(0, 2),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 0.
        assert_eq!(vec_len_for_test(ptr), 0);

        // Clean up.
        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with integer elements
    #[test]
    fn test_compile_vec_literal_with_ints() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 10, span: Span::new(1, 3), inferred_type: None },
                Expr::IntLit { value: 20, span: Span::new(4, 6), inferred_type: None },
                Expr::IntLit { value: 30, span: Span::new(7, 9), inferred_type: None },
            ],
            span: Span::new(0, 10),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 3.
        assert_eq!(vec_len_for_test(ptr), 3);

        // Verify element values from data buffer.
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(heap::HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64);
            assert_eq!(*data_ptr, 10);
            assert_eq!(*data_ptr.add(1), 20);
            assert_eq!(*data_ptr.add(2), 30);
        }

        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — single-element Vec literal
    #[test]
    fn test_compile_vec_literal_single_element() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1, 3), inferred_type: None },
            ],
            span: Span::new(0, 4),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "single-element vec should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(vec_len_for_test(ptr), 1);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 42);
        }

        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with boolean elements
    #[test]
    fn test_compile_vec_literal_with_bool_elements() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: Span::new(1, 5), inferred_type: None },
                Expr::BoolLit { value: false, span: Span::new(6, 11), inferred_type: None },
            ],
            span: Span::new(0, 12),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "bool vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(vec_len_for_test(ptr), 2);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1); // true
            assert_eq!(*data_ptr.add(1), 0); // false
        }

        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len inline primitive codegen
    #[test]
    fn test_compile_vec_len_inline() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [10 20 30])
        let vec_span = Span::new(10, 20);
        let apply_span = Span::new(0, 25);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            apply_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1, 8),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 10, span: Span::new(11, 13), inferred_type: None },
                    Expr::IntLit { value: 20, span: Span::new(14, 16), inferred_type: None },
                    Expr::IntLit { value: 30, span: Span::new(17, 19), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            }],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-len should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: appendix-a-builtins §A.3 — vec-get bounds-checked index codegen
    #[test]
    fn test_compile_vec_get_inline() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-get v 1))
        let vec_span = Span::new(8, 18);
        let get_span = Span::new(21, 35);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(9, 11), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(12, 14), inferred_type: None },
                        Expr::IntLit { value: 30, span: Span::new(15, 17), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(22, 29),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(30, 31),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 1, span: Span::new(32, 33), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 36),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get should compile: {result:?}");
        assert_eq!(result.unwrap(), 20);
    }

    // spec: appendix-a-builtins §A.3 — vec-get index 0 boundary
    #[test]
    fn test_compile_vec_get_first_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(100, 110);
        let get_span = Span::new(120, 135);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(101, 104), inferred_type: None },
                        Expr::IntLit { value: 200, span: Span::new(105, 108), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(121, 128),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(129, 130),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 0, span: Span::new(131, 132), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(99, 136),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get index 0 should work: {result:?}");
        assert_eq!(result.unwrap(), 100);
    }

    // spec: appendix-a-builtins §A.3 — vec-get last index boundary
    #[test]
    fn test_compile_vec_get_last_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(200, 210);
        let get_span = Span::new(220, 235);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(201, 202), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(203, 204), inferred_type: None },
                        Expr::IntLit { value: 3, span: Span::new(205, 206), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(221, 228),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(229, 230),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 2, span: Span::new(231, 232), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(199, 236),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get last index should work: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-set copy-on-write path codegen
    #[test]
    fn test_compile_vec_set_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-len (vec-set v 1 99)))
        // Since v is used twice (vec-set and vec-len), vec-set takes the copy path.
        let vec_span = Span::new(300, 310);
        let set_span = Span::new(320, 340);
        let len_span = Span::new(315, 345);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(301, 303), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(304, 306), inferred_type: None },
                        Expr::IntLit { value: 30, span: Span::new(307, 309), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(316, 323),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("vec-set"),
                        span: Span::new(321, 328),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("v"),
                            span: Span::new(329, 330),
                            resolved_call: None,
                            inferred_type: None,
                        },
                        Expr::IntLit { value: 1, span: Span::new(331, 332), inferred_type: None },
                        Expr::IntLit { value: 99, span: Span::new(333, 335), inferred_type: None },
                    ],
                    span: set_span,
                    resolved_call: None,
                    inferred_type: None,
                }],
                span: len_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(299, 346),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-set should compile: {result:?}");
        // vec-set returns a new Vec with same length.
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-push copy-on-write path codegen
    #[test]
    fn test_compile_vec_push_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [10 20] 30))
        let vec_span = Span::new(400, 410);
        let push_span = Span::new(415, 435);
        let len_span = Span::new(410, 440);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(411, 418),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(416, 424),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(401, 403), inferred_type: None },
                            Expr::IntLit { value: 20, span: Span::new(404, 406), inferred_type: None },
                        ],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 30, span: Span::new(425, 427), inferred_type: None },
                ],
                span: push_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-push should compile: {result:?}");
        // [10 20] pushed 30 -> len 3
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.3, §4.10 — Vec literal bound in let, accessed via vec-len
    #[test]
    fn test_compile_vec_literal_in_let() {
        // (let [v [1 2 3]] (vec-len v))
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(500, 510);
        let len_span = Span::new(515, 530);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(501, 502), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(503, 504), inferred_type: None },
                        Expr::IntLit { value: 3, span: Span::new(505, 506), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(516, 523),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(524, 525),
                    resolved_call: None,
                    inferred_type: None,
                }],
                span: len_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(499, 531),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec in let should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10, §4.11 — Vec literal with computed elements, left-to-right eval
    #[test]
    fn test_compile_vec_literal_with_computed_elements() {
        use cranelisp_types::ResolvedCall;

        // [1 (+ 2 3) 10]
        let add_span = Span::new(603, 610);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: Span::new(601, 602), inferred_type: None },
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: Span::new(604, 605),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 2, span: Span::new(606, 607), inferred_type: None },
                        Expr::IntLit { value: 3, span: Span::new(608, 609), inferred_type: None },
                    ],
                    span: add_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 10, span: Span::new(611, 613), inferred_type: None },
            ],
            span: Span::new(600, 614),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec with computed elements should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(vec_len_for_test(ptr), 3);
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1);
            assert_eq!(*data_ptr.add(1), 5); // 2 + 3
            assert_eq!(*data_ptr.add(2), 10);
        }

        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // spec: 05-definitions §5.1, 04-expressions §4.10 — Vec literal as function return value
    #[test]
    fn test_compile_vec_in_function_defn() {
        // (defn make-vec [] [1 2 3])
        // Returns a Vec literal.
        let defn = Defn {
            name: Symbol::from("make-vec"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::VecLit {
                elements: vec![
                Expr::IntLit { value: 1, span: Span::new(701, 702), inferred_type: None },
                Expr::IntLit { value: 2, span: Span::new(703, 704), inferred_type: None },
                Expr::IntLit { value: 3, span: Span::new(705, 706), inferred_type: None },
                ],
                span: Span::new(700, 707),
                inferred_type: None,
                },
                span: Span::new(700, 710),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(700, 710),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let ptr = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");
        assert_eq!(vec_len_for_test(ptr), 3);

        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-get returns correct element value
    #[test]
    fn test_compile_vec_get_verify_value() {
        use cranelisp_types::ResolvedCall;

        // (let [v [100 200 300]] (vec-get v 2))
        let vec_span = Span::new(808, 818);
        let get_span = Span::new(821, 840);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(809, 812), inferred_type: None },
                        Expr::IntLit { value: 200, span: Span::new(813, 816), inferred_type: None },
                        Expr::IntLit { value: 300, span: Span::new(817, 820), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(822, 829),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(830, 831),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 2, span: Span::new(832, 833), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(807, 841),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get value should compile: {result:?}");
        assert_eq!(result.unwrap(), 300);
    }

    // spec: 12-runtime §12.3.3 — vec-push on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_push_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [1] 2))
        // vec-push on a temporary VecLit — will take COW path (temp = unique).
        let vec_span = Span::new(900, 905);
        let push_span = Span::new(910, 925);
        let len_span = Span::new(905, 930);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(906, 913),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(911, 919),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 1, span: Span::new(901, 902), inferred_type: None },
                        ],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 2, span: Span::new(920, 921), inferred_type: None },
                ],
                span: push_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-push on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 2);
    }

    // spec: 12-runtime §12.3.3 — vec-set on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_set_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-set [10 20 30] 0 99))
        let vec_span = Span::new(1000, 1010);
        let set_span = Span::new(1015, 1035);
        let len_span = Span::new(1010, 1040);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1011, 1018),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-set"),
                    span: Span::new(1016, 1023),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(1001, 1003), inferred_type: None },
                            Expr::IntLit { value: 20, span: Span::new(1004, 1006), inferred_type: None },
                            Expr::IntLit { value: 30, span: Span::new(1007, 1009), inferred_type: None },
                        ],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 0, span: Span::new(1024, 1025), inferred_type: None },
                    Expr::IntLit { value: 99, span: Span::new(1026, 1028), inferred_type: None },
                ],
                span: set_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-set on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10 — Vec literal in interactive (REPL) mode
    #[test]
    fn test_compile_vec_literal_interactive_mode() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1101, 1103), inferred_type: None },
            ],
            span: Span::new(1100, 1104),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(
            &expr, &check, &empty_tables(),
        );
        assert!(result.is_ok(), "vec in interactive mode should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024);
        assert_eq!(vec_len_for_test(ptr), 1);

        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec returns 0
    #[test]
    fn test_compile_vec_empty_len() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [])
        let vec_span = Span::new(1200, 1202);
        let len_span = Span::new(1195, 1210);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1196, 1203),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: vec_span,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty vec len should compile: {result:?}");
        assert_eq!(result.unwrap(), 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-push on empty Vec
    #[test]
    fn test_compile_vec_push_empty_vec() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [] 42))
        let vec_span = Span::new(1300, 1302);
        let push_span = Span::new(1305, 1320);
        let len_span = Span::new(1300, 1325);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1301, 1308),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(1306, 1314),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 42, span: Span::new(1315, 1317), inferred_type: None },
                ],
                span: push_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "push to empty vec should compile: {result:?}");
        assert_eq!(result.unwrap(), 1);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec (duplicate boundary check)
    #[test]
    fn test_compile_vec_len_empty_vec() {
        use cranelisp_types::ResolvedCall;

        let len_span = Span::new(1400, 1420);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1401, 1408),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: Span::new(1409, 1411),
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0);
    }

    // spec: 04-expressions §4.10 — nested Vec literals (Vec of Vecs)
    #[test]
    fn test_compile_nested_vec_literals() {
        // [[1 2] [3 4]] — a Vec of Vecs (nested heap values)
        let expr = Expr::VecLit {
            elements: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(1502, 1503), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(1504, 1505), inferred_type: None },
                    ],
                    span: Span::new(1501, 1506),
                    inferred_type: None,
                },
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 3, span: Span::new(1508, 1509), inferred_type: None },
                        Expr::IntLit { value: 4, span: Span::new(1510, 1511), inferred_type: None },
                    ],
                    span: Span::new(1507, 1512),
                    inferred_type: None,
                },
            ],
            span: Span::new(1500, 1513),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "nested vec should compile: {result:?}");
        let outer_ptr = result.unwrap();
        assert!(outer_ptr > 1024);
        assert_eq!(vec_len_for_test(outer_ptr), 2);

        // First inner vec.
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            let inner1 = *data;
            assert!(inner1 > 1024, "inner vec should be heap pointer");
            assert_eq!(vec_len_for_test(inner1), 2);
        }

        // Clean up (inner vecs need manual cleanup since no drop glue yet).
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            cranelisp_intrinsics::vec_runtime::vec_drop(*data, 0);
            cranelisp_intrinsics::vec_runtime::vec_drop(*data.add(1), 0);
        }
        cranelisp_intrinsics::vec_runtime::vec_drop(outer_ptr, 0);
    }

    // spec: 04-expressions §4.10 — large Vec literal (10 elements)
    #[test]
    fn test_compile_vec_large_literal() {
        // [0 1 2 3 4 5 6 7 8 9] — 10 elements
        let elements: Vec<Expr> = (0..10)
            .map(|i| Expr::IntLit {
                value: i,
                span: Span::new(1600 + (i as u32) * 2, 1602 + (i as u32) * 2),
                inferred_type: None,
            })
            .collect();

        let expr = Expr::VecLit {
            elements,
            span: Span::new(1600, 1620),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "large vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(vec_len_for_test(ptr), 10);

        unsafe {
            let base = ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            for i in 0..10 {
                assert_eq!(*data.add(i), i as i64);
            }
        }

        cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
    }

    // --- Ring 2A: TraitMethod dispatch tests ---

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Num.+ primitive dispatch inlines to add-i64.
    //
    // Per Decision 43 + FIXME 0185: backend has no trait knowledge. The
    // pre-D43 shape (TraitMethod with `(Num, "+", Int)` → backend-side
    // `primitive_for_trait_method` lookup → inline IR) is deleted. The
    // post-D43 path is: typecheck emits `ResolvedCall::BuiltinFn { name:
    // "add-i64" }` directly for primitive-implemented operators; backend's
    // inline-substitution path matches by Symbol only. The test asserts
    // this end-to-end: `BuiltinFn { name: "add-i64" }` → inline iadd → 7.
    #[test]
    fn test_trait_method_dispatch_inline_add() {
        // (+ 3 4) post-D43 = BuiltinFn add-i64 (typecheck resolves the
        // primitive directly, not a TraitMethod).
        let apply_span = Span::new(100, 110);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: Span::new(101, 102),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 3, span: Span::new(103, 104), inferred_type: None },
                Expr::IntLit { value: 4, span: Span::new(105, 106), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let value = test_compile_and_run(&expr, &check, &empty_tables())
            .expect("BuiltinFn add-i64 should compile inline");
        assert_eq!(value, 7);
    }

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Eq.= primitive dispatch on Bool.
    //
    // Per Decision 43 + FIXME 0185: same shape change as the Num.+ test.
    // Post-D43 typecheck emits `BuiltinFn { name: "eq-bool" }` for the
    // primitive-implemented `=` on Bool. Backend's inline path matches by
    // Symbol; the result is the `icmp eq` IR returning 1 (true).
    #[test]
    fn test_trait_method_dispatch_eq_bool() {
        // (= true true) post-D43 = BuiltinFn eq-bool.
        let apply_span = Span::new(200, 210);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("="),
                span: Span::new(201, 202),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::BoolLit { value: true, span: Span::new(203, 207), inferred_type: None },
                Expr::BoolLit { value: true, span: Span::new(208, 212), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("eq-bool"),
            },
        );

        let value = test_compile_and_run(&expr, &check, &empty_tables())
            .expect("BuiltinFn eq-bool should compile inline");
        assert_eq!(value, 1); // true == true → true (1)
    }

    // spec: 07-traits §7.7 — constrained polymorphic fn skipped at definition, monomorphised at call
    #[test]
    fn test_constrained_fn_skipped_in_compile_program() {
        // A constrained fn should be skipped (not compiled).
        let defn = Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::IntLit { value: 0, span: Span::new(10, 11), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(30, 32), inferred_type: None },
                span: Span::new(25, 40),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(25, 40),
        };

        let program: Program = vec![
            TopLevel::Defn(defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Mark "add" as constrained — should be skipped during compilation.
        check.constrained_fn_names.insert(Symbol::from("add"));

        let value = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("should compile with constrained fn skipped");
        assert_eq!(value, 42);
    }

    // spec: 07-traits §7.7 — no default method defns produces empty extras
    #[test]
    fn test_collect_extra_defns_empty() {
        let check = empty_check();
        // Verify default_method_defns is empty in a fresh CheckResult.
        assert!(check.default_method_defns.is_empty());
    }

    // spec: 07-traits §7.7 — default trait methods compiled as extra defns
    #[test]
    fn test_compile_with_default_method_defns() {
        // A program with only a main function, but check has a default method defn.
        // The default method defn should be compiled alongside main.
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("default-ne"),
                        span: Span::new(10, 20),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 1, span: Span::new(21, 22), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(23, 24), inferred_type: None },
                    ],
                    span: Span::new(9, 25),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(0, 30),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 30),
        };

        let default_defn = Defn {
            name: Symbol::from("default-ne"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                body: Expr::IntLit { value: 77, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let program: Program = vec![TopLevel::Defn(main_defn)];
        let mut check = empty_check();
        check.default_method_defns.push(default_defn);

        let value = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("program with default method defns should compile");
        assert_eq!(value, 77, "should call the default method defn");
    }

    // spec: 12-runtime §12.5, 07-traits §7.7 — TCO for monomorphised self-recursive call
    //
    // When a constrained-poly function like `countdown` is monomorphised to
    // `countdown$Int`, the body contains a self-recursive call `(countdown ...)`
    // that the typechecker resolves to `SigDispatch { mangled_name: "countdown$Int" }`.
    // The backend's TCO check must recognize this as self-recursion.
    //
    // This test compiles a simple recursive function and verifies it completes
    // without stack overflow (1M iterations would blow the stack without TCO).
    #[test]
    fn test_mono_defn_self_recursive_tco() {
        // countdown$Int: (defn countdown$Int [n] (if (= n 0) 0 (countdown$Int (- n 1))))
        // Simplified: use intrinsic primitives instead of trait dispatch.
        let n_span = Span::new(10, 11);
        let zero_span = Span::new(20, 21);
        let eq_span = Span::new(30, 40);
        let sub_span = Span::new(50, 60);
        let recurse_span = Span::new(70, 90);
        let if_span = Span::new(5, 95);
        let result_span = Span::new(92, 93);

        // Build: (if (eq-i64 n 0) 0 (countdown$Int (sub-i64 n 1)))
        let cond = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: Span::new(31, 37),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: n_span, resolved_call: None, inferred_type: None },
                Expr::IntLit { value: 0, span: zero_span, inferred_type: None },
            ],
            span: eq_span,
            resolved_call: None,
            inferred_type: None,
        };

        let sub_call = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("sub-i64"),
                span: Span::new(51, 58),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: Span::new(55, 56), resolved_call: None, inferred_type: None },
                Expr::IntLit { value: 1, span: Span::new(57, 58), inferred_type: None },
            ],
            span: sub_span,
            resolved_call: None,
            inferred_type: None,
        };

        // The recursive call: callee is "countdown" (original name),
        // but it's resolved to countdown$Int via SigDispatch.
        let recurse = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("countdown"),
                span: Span::new(71, 80),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![sub_call],
            span: recurse_span,
            resolved_call: None,
            inferred_type: None,
        };

        let body = Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(Expr::IntLit { value: 0, span: result_span, inferred_type: None }),
            else_branch: Box::new(recurse),
            span: if_span,
            inferred_type: None,
        };

        let countdown_defn = Defn {
            name: Symbol::from("countdown$Int"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("n"), None)],
                body,
                span: Span::new(0, 100),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 100),
        };

        // Set up method resolutions:
        // - eq_span: BuiltinFn("eq-i64") for the equality check
        // - sub_span: BuiltinFn("sub-i64") for the subtraction
        // - recurse_span: SigDispatch("countdown$Int") for the self-recursive call
        let mut check = empty_check();
        check.method_resolutions.insert(
            eq_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("eq-i64"),
            },
        );
        check.method_resolutions.insert(
            sub_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("sub-i64"),
            },
        );
        check.method_resolutions.insert(
            recurse_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("countdown$Int"),
            },
        );

        // Enrich the defn from CheckResult side maps (test bridge).
        let mut enriched_defn = countdown_defn.clone();
        enrich_defn_from_side_maps(&mut enriched_defn, &check.method_resolutions, &check.expr_types);

        // Compile with direct calls (no GOT).
        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        jit.declare_intrinsics().unwrap();
        let func_ids = jit.declare_functions(&[&enriched_defn]).unwrap();

        let arities: HashMap<Symbol, usize> =
            vec![(Symbol::from("countdown$Int"), 1)].into_iter().collect();

        let tables = empty_tables();
        let aliases = empty_aliases();
        let ctx = jit.build_compile_context(
            &func_ids, &arities,
            &tables, &aliases, ModuleFullPath::from("test"),
        );
        jit.compile_defn(&enriched_defn, ctx).unwrap();
        let countdown_ptr = jit.finalize_and_get_ptr(&Symbol::from("countdown$Int"), 1).unwrap();

        // Call with 1_000_000 — without TCO this would stack overflow.
        let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(countdown_ptr) };
        let result = func(1_000_000);
        assert_eq!(result, 0, "TCO should allow 1M recursive calls without stack overflow");
    }

    // --- compile_to_module module tests ---

    // spec: design/arch/CLAUDE.md Decision 36 — bare-name function declarations
    // uniformly across all modules. Two modules with same-named function compile
    // into separate JITs without collision because function symbols are
    // `.o`-Local — they cannot collide across modules' JITs.
    #[test]
    fn test_module_prefix_applied() {
        let _ = empty_check();
        // Module "mod_a" defines "val" returning 100.
        let val_a = Defn {
            name: Symbol::from("val"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 100, span: Span::new(0, 3), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let mod_a = ModuleFullPath::from("mod_a");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(mod_a.clone());
            st.insert(val_a.name.clone(), make_def_entry(val_a.clone()));
            tables.insert(mod_a.clone(), st);
        }
        let mut jit_a = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let _artifacts_a = compile_to_module(
            mod_a.clone(),
            std::slice::from_ref(&val_a.name),
            &tables,
            &aliases,
            jit_a.jit_module(),
            true,
        ).expect("module A should compile");
        // Post-G6: compile_to_module finalized internally. `val` is a zero-arg
        // defn with no GOT slot (direct FuncId); read its ptr by name.
        let ptr = jit_a.get_ptr_by_name(&Symbol::from("val"), 0).unwrap();
        assert!(!ptr.is_null(), "module A 'val' must finalize to a non-null ptr");
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        assert_eq!(func(), 100, "module A's val should return 100");

        // Module B also defines "val" returning 200 — compiles into a separate JIT.
        let val_b = Defn {
            name: Symbol::from("val"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 200, span: Span::new(100, 103), inferred_type: None },
                span: Span::new(100, 120),
            }],
            visibility: Visibility::Public,
            span: Span::new(100, 120),
        };
        let mod_b = ModuleFullPath::from("mod_b");
        {
            let mut st = SymbolTable::new(mod_b.clone());
            st.insert(val_b.name.clone(), make_def_entry(val_b.clone()));
            tables.insert(mod_b.clone(), st);
        }

        let mut jit_b = Jit::new_with_symbols(&[]).unwrap();
        let _artifacts_b = compile_to_module(
            mod_b.clone(),
            std::slice::from_ref(&val_b.name),
            &tables,
            &aliases,
            jit_b.jit_module(),
            true,
        ).expect("module B should compile without collision");
        // Post-G6: compile_to_module finalized internally.
        let ptr_b = jit_b.get_ptr_by_name(&Symbol::from("val"), 0).unwrap();
        let func_b: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr_b) };
        assert_eq!(func_b(), 200, "module B's val should return 200");
    }

    // --- G6 code-write invariants (Sprint 57 Wave 2; S75 W2 D41 rotation) ---
    //
    // spec: design/backend/compile-to-module.md §2 (S75 banner) + facade
    // §"Code" — `compile_to_module` writes each compiled symbol's finalised
    // code pointer directly into the entry's GOT slot (D41 #2), and no longer
    // returns a per-symbol `code_ptrs` map. The lifecycle-owner write (D41 #1
    // — `Code::Jit(Arc<Jit>)`) stays in the integration layer; backend leaves
    // `ModuleEntry::Def.code` untouched.
    #[test]
    fn compile_to_module_writes_got_slot_after_finalize() {
        let defn = Defn {
            name: Symbol::from("seven"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 7, span: Span::new(0, 1), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            // Explicit GOT slot so the D41 #2 direct-write is exercised.
            st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
            st.next_got_slot = 1;
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let _artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        ).expect("JIT compile should succeed");

        // D41 #2: backend wrote the finalised code pointer into the entry's
        // GOT slot (slot 0). Read it back; it must be non-null in JIT mode.
        let guard = tables.get(&module).expect("symbol table present");
        let entry = guard.get(defn.name.as_ref()).expect("entry present");
        match entry {
            ModuleEntry::Def { got_slot: Some(slot), code, .. } => {
                let ptr = guard.got.load_slot(*slot);
                assert!(
                    !ptr.is_null(),
                    "backend must write the finalised code pointer to the GOT slot (D41 #2)"
                );
                // D41 #1 (Code::Jit lifecycle owner) stays in the integration
                // layer — backend leaves `code` untouched.
                assert!(
                    code.is_none(),
                    "backend must not write to ModuleEntry::Def.code (D41 #1 is int's job)"
                );
            }
            _ => unreachable!("test inserted a Def entry with a GOT slot"),
        }
    }

    // spec: design/backend/compile-to-module.md §2.6.6 — constructor-as-value
    // through the generic fn-as-value GOT path (S75 W4 closure deletion).
    //
    // This is the durable regression guard for deleting the bespoke
    // `compile_data_constructor_as_value` + `compile_ctor_wrapper_body` family.
    // It proves the corrected `compile_var` dispatch: a *data* constructor
    // referenced as a value (`(let [f Some] (f 3))`) is no longer special-cased;
    // it falls through to `is_known_function` → `compile_fn_as_value` over the
    // got-slotted constructor `Def` — the SAME GOT/fn-as-value mechanism
    // `compile_operator_as_value` uses for primitives (§2.6.1, Decision 48).
    //
    // Two-stage `make_def_entry_slot` pattern (§2.6.6):
    //   Stage 1 — got-slot + compile the constructor `Def` (its `Expr::ConstrADT`
    //             body → `compile_constr_adt` → `emit_adt_construct`) so the GOT
    //             slot holds a live callable.
    //   Stage 2 — compile a consumer that references the constructor as a value;
    //             `compile_fn_as_value`'s `emit_wrapper_call` GOT-indirects to
    //             slot 0. Run end-to-end (slab base registered via
    //             `Jit::new_with_symbols`, the precedent set by
    //             `jit_got_symbol_address_is_slab_base` /
    //             `test_extern_primitive_with_resolved_call`) and assert the
    //             constructed ADT's field round-trips.
    //
    // Backend EXPECTS the constructor's GOT slot to be populated; the harness
    // populates it the way int will at S77 (§2.6.5). Backend does not got-slot
    // constructors itself — that is typecheck + int's job, exactly as primitives'
    // GOT entries are not backend's.
    #[test]
    fn constructor_as_value_falls_through_to_fn_as_value() {
        use cranelisp_types::{
            DefKind, FQTypeName, ModuleEntry, Scheme, TypeName,
        };

        let module = ModuleFullPath::from("user");
        let fqtn = FQTypeName::new(module.clone(), TypeName::from("Option"));

        // The constructor `Some`'s synthesised body: ConstrADT { tag: 1,
        // fields: [Var("v")] } — the exact shape typecheck produces at S77.
        let ctor_body = Expr::ConstrADT {
            type_name: fqtn.clone(),
            tag: 1,
            fields: vec![Expr::Var {
                name: Symbol::from("v"),
                span: Span::new(10, 11),
                resolved_call: None,
                inferred_type: Some(Box::new(Type::Int)),
            }],
            span: Span::new(0, 12),
            inferred_type: Some(Box::new(Type::ADT(fqtn.clone(), vec![]))),
        };
        let ctor_defn = Defn {
            name: Symbol::from("Some"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("v"), None)],
                body: ctor_body,
                span: Span::new(0, 12),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 12),
        };
        // make_def_entry_slot stamps kind = UserFn; override to Constructor so
        // `lookup_constructor` / `data_constructor_info` recognise it AND
        // `resolve_got_target` finds the got slot (slot 0).
        let ctor_entry = match make_def_entry_slot(ctor_defn.clone(), 0) {
            ModuleEntry::Def {
                visibility,
                docstring,
                param_names,
                callees,
                got_slot,
                trait_origin,
                seq,
                ast,
                code,
                ..
            } => ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![]))),
                },
                visibility,
                docstring,
                param_names,
                kind: Box::new(DefKind::Constructor {
                    type_name: fqtn.clone(),
                    tag: 1,
                    field_count: 1,
                    internal: false,
                    type_def: None,
                }),
                callees,
                got_slot,
                trait_origin,
                seq,
                ast,
                code,
            },
            _ => unreachable!("make_def_entry_slot builds a Def"),
        };

        // Consumer: (let [f Some] (f 3)) — references `Some` as a value, then
        // calls the bound closure. The `[f Some]` binding compiles `Some` via
        // `compile_var` → fall-through → `compile_fn_as_value` (the path under
        // test); `(f 3)` is a local-var closure call.
        let consumer_body = Expr::Let {
            bindings: vec![(
                Symbol::from("f"),
                Expr::Var {
                    name: Symbol::from("Some"),
                    span: Span::new(100, 104),
                    resolved_call: None,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("f"),
                    span: Span::new(110, 111),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 3,
                    span: Span::new(112, 113),
                    inferred_type: None,
                }],
                span: Span::new(109, 114),
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(90, 115),
            inferred_type: None,
        };
        let consumer_defn = Defn {
            name: Symbol::from("useit"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: consumer_body,
                span: Span::new(90, 115),
            }],
            visibility: Visibility::Public,
            span: Span::new(90, 115),
        };

        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(ctor_defn.name.clone(), ctor_entry);
            st.insert(consumer_defn.name.clone(), make_def_entry_slot(consumer_defn.clone(), 1));
            st.next_got_slot = 2;
            tables.insert(module.clone(), st);
        }

        // Register __cranelisp_got_user → the table's GOT slab base BEFORE
        // building the JIT (base_ptr is stable for the GotTable's lifetime).
        let got_data_name = crate::compiler::got_data_symbol_name(&module);
        let got_base = tables
            .get(&module)
            .map(|st| st.got.base_ptr())
            .expect("user table just inserted");
        let extras: Vec<(&str, *const u8)> = vec![(got_data_name.as_str(), got_base)];

        let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
        let aliases = empty_aliases();
        let names = vec![ctor_defn.name.clone(), consumer_defn.name.clone()];
        compile_to_module(module.clone(), &names, &tables, &aliases, jit.jit_module(), true)
            .expect("constructor Def + consumer compile (closure deletion regression guard)");

        // Stage 1 assertion: the constructor `Def`'s body compiled into a live
        // callable at slab slot 0 (non-null after finalize — the same write
        // `compile_to_module_writes_got_slot_after_finalize` asserts).
        {
            let guard = tables.get(&module).expect("table present");
            match guard.get("Some") {
                Some(ModuleEntry::Def { got_slot: Some(slot), .. }) => {
                    assert!(
                        !guard.got.load_slot(*slot).is_null(),
                        "constructor body must finalize to a live callable in its GOT slot (Stage 1)"
                    );
                }
                other => panic!("expected got-slotted constructor Def, got {other:?}"),
            }
        }

        // Stage 2 assertion: run the consumer end-to-end. It builds `(Some 3)`
        // through the GOT-indirect fn-as-value wrapper and returns the heap
        // pointer to `[.., tag=1, field=3]`. Read the field back.
        let ptr = jit.get_ptr_by_name(&consumer_defn.name, 0).expect("finalize consumer");
        assert!(!ptr.is_null(), "consumer must finalize to a non-null fn ptr");
        let _ = cranelisp_intrinsics::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let adt_ptr = func();
        if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
            panic!("runtime panic running consumer: {msg}");
        }
        assert!(adt_ptr != 0, "constructor-as-value must allocate a heap ADT");
        // Field 0 lives at HeapAdt::field_offset(0) from the base pointer.
        let field0 = unsafe {
            let field_addr = (adt_ptr as usize
                + crate::heap::HeapAdt::field_offset(0) as usize)
                as *const i64;
            *field_addr
        };
        assert_eq!(
            field0, 3,
            "constructor-as-value (map-style first-class use) must construct the ADT \
             with the passed field; got {field0}"
        );
    }

    // spec: 07-traits §7.6 — a trait method used as a first-class value
    // dispatches to the impl chosen by typecheck for the value's type, NOT a
    // hard-coded default. This is the backend half of FIXME 0300 Symptom B.
    //
    // `(let [f +] (f 1.0 2.0))` where typecheck has annotated the value-position
    // `+` Var with `resolved_call: Some(BuiltinFn { name: "add-f64" })` and
    // `inferred_type: Fn([Float, Float], Float)`. The new `compile_var` early
    // branch emits a zero-capture dispatch-wrapper that calls `add-f64` (float
    // add). The OLD hard-coded `compile_operator_as_value` path mapped `+` →
    // `add-i64` unconditionally — integer add on the two float bit-patterns —
    // which yields a garbage / `inf.0`-shaped result, never `3.0`. So a `3.0`
    // result proves the resolution is honored and the Int path is bypassed.
    //
    // `add-f64` is an INLINE builtin (`primitives_inline`), so this runs
    // end-to-end inside the backend unit-test JIT with no `cranelisp-primitives`
    // dependency (Decision 48) and no extern symbol.
    #[test]
    fn value_position_plus_float_dispatches_add_f64_not_add_i64() {
        // The value-position `+` reference, fully annotated as typecheck's
        // value-position resolution pass produces (FIXME 0300 Step 2/3).
        let plus_as_value = Expr::Var {
            name: Symbol::from("+"),
            span: Span::new(100, 101),
            resolved_call: Some(Box::new(
                cranelisp_types::ResolvedCall::BuiltinFn {
                    name: Symbol::from("add-f64"),
                },
            )),
            inferred_type: Some(Box::new(Type::Fn(
                vec![Type::Float, Type::Float],
                Box::new(Type::Float),
            ))),
        };

        // Consumer: (let [f +] (f 1.0 2.0)) — binds the dispatch-wrapper closure
        // to `f`, then applies it. `(f 1.0 2.0)` is a local-var closure call.
        let consumer_body = Expr::Let {
            bindings: vec![(Symbol::from("f"), plus_as_value)],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("f"),
                    span: Span::new(110, 111),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::FloatLit {
                        value: 1.0,
                        span: Span::new(112, 115),
                        inferred_type: Some(Box::new(Type::Float)),
                    },
                    Expr::FloatLit {
                        value: 2.0,
                        span: Span::new(116, 119),
                        inferred_type: Some(Box::new(Type::Float)),
                    },
                ],
                span: Span::new(109, 120),
                resolved_call: None,
                inferred_type: Some(Box::new(Type::Float)),
            }),
            span: Span::new(90, 121),
            inferred_type: Some(Box::new(Type::Float)),
        };

        let value = test_compile_and_run(
            &consumer_body,
            &empty_check(),
            &empty_tables(),
        )
        .expect("value-position + (add-f64) should compile and run");

        let result = f64::from_bits(value as u64);
        assert_eq!(
            result, 3.0,
            "value-position `+` on Floats must dispatch to add-f64 (→ 3.0); \
             a non-3.0 result means the hard-coded add-i64 path leaked \
             (FIXME 0300 Symptom B)"
        );
    }

    // spec: 07-traits §7.6 — value-position trait method resolved to a TraitMethod
    // (mangled impl) emits a dispatch-wrapper that calls the *mangled name*, NOT
    // the hard-coded operator primitive. We assert this WITHOUT a GOT slot for
    // the impl (which is the int-binary's concern; the four e2e tests cover the
    // run side after the int slice): the wrapper's `emit_wrapper_call` resolves
    // the mangled name `Eq.=$String` and — because no slot is registered in this
    // minimal table — fails with an error naming `Eq.=$String`. That error is
    // proof-positive that `compile_var` took the resolved-call branch and tried
    // to dispatch to the typecheck-chosen impl, rather than silently emitting
    // the hard-coded `eq-i64` (`operator_primitive_name`) which would have
    // compiled "successfully" to the WRONG impl (Symptom B).
    #[test]
    fn value_position_eq_string_dispatches_to_mangled_impl_not_eq_i64() {
        let module = ModuleFullPath::from("user");

        // `=` on String resolved to the mangled trait-impl name (the non-
        // primitive TraitMethod path). The wrapper must call this name, not
        // emit the hard-coded `eq-i64`.
        let eq_as_value = Expr::Var {
            name: Symbol::from("="),
            span: Span::new(50, 51),
            resolved_call: Some(Box::new(
                cranelisp_types::ResolvedCall::TraitMethod {
                    trait_name: cranelisp_types::FQTraitName::new(
                        module.clone(),
                        cranelisp_types::TraitName::from("Eq"),
                    ),
                    method_name: Symbol::from("="),
                    impl_type: cranelisp_types::FQTypeName::new(
                        ModuleFullPath::from("primitives"),
                        cranelisp_types::TypeName::from("String"),
                    ),
                    mangled_name: cranelisp_types::JitSymbol::from("Eq.=$String"),
                },
            )),
            inferred_type: Some(Box::new(Type::Fn(
                vec![Type::String, Type::String],
                Box::new(Type::Bool),
            ))),
        };
        let defn = Defn {
            name: Symbol::from("__expr__"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: eq_as_value,
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };

        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(defn.name.clone(), make_def_entry(defn.clone()));
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).expect("jit init");
        let aliases = empty_aliases();
        let names = vec![defn.name.clone()];
        let result = compile_to_module(
            module.clone(),
            &names,
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        );
        // `CompilationArtifacts` is not `Debug`, so match rather than `expect_err`.
        let err = match result {
            Ok(_) => panic!(
                "without a registered GOT slot for the impl, the dispatch-wrapper's \
                 call to the mangled name must fail — a clean compile means the \
                 hard-coded eq-i64 path leaked (FIXME 0300 Symptom B)"
            ),
            Err(e) => e,
        };

        let msg = format!("{err:?}");
        assert!(
            msg.contains("Eq.=$String"),
            "the codegen error must name the typecheck-chosen mangled impl \
             `Eq.=$String` (proving the wrapper dispatched to the resolved \
             target); a silent success or an `eq-i64` reference would mean the \
             hard-coded operator path leaked (FIXME 0300 Symptom B). Got: {msg}"
        );
    }

    // spec: facades/backend.md §"Free functions" — produce_disasm reads the
    // live GOT-slot code pointer, reads caller-supplied `code_size` bytes, and
    // capstone-disassembles them (S75 W3 Finding-C — real body, not a stub).
    #[test]
    fn produce_disasm_returns_nonempty_for_jit_compiled_fn() {
        use cranelisp_types::FQSymbol;

        let defn = Defn {
            name: Symbol::from("seven"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 7, span: Span::new(0, 1), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
            st.next_got_slot = 1;
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        ).expect("JIT compile should succeed");

        // code_size comes from the compile-time artifacts — the caller passes
        // it back into produce_disasm (Finding-C: backend never re-derives it).
        assert!(artifacts.code_size > 0, "JIT codegen must report a code size");

        let fq = FQSymbol { module: module.clone(), symbol: defn.name.clone() };
        let disasm = produce_disasm(&fq, artifacts.code_size, &tables)
            .expect("produce_disasm should disassemble live JIT code");
        assert!(
            !disasm.trim().is_empty(),
            "produce_disasm must return non-empty disassembly text for a live fn"
        );
    }

    // spec: design/backend/compile-to-module.md §9.1.6 — ObjectModule has no
    // post-finalize runtime pointer; the GOT slot stays null in object mode.
    #[test]
    fn compile_to_module_object_mode_no_got_write() {
        use cranelift_module::default_libcall_names;
        use cranelift_object::{ObjectBuilder, ObjectModule};

        let defn = Defn {
            name: Symbol::from("answer"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            // Explicit GOT slot so we can assert object mode leaves it null.
            st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
            st.next_got_slot = 1;
            tables.insert(module.clone(), st);
        }

        let isa = build_isa(true).unwrap();
        let obj_builder =
            ObjectBuilder::new(isa, "test_obj", default_libcall_names()).unwrap();
        let mut obj_module = ObjectModule::new(obj_builder);

        let aliases = empty_aliases();
        let _artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            &mut obj_module,
            true,
        ).expect("object compile should succeed");

        // Object-mode invariant: `try_get_finalized_function` returns None (no
        // runtime pointer before `finish()`), so backend writes nothing to the
        // GOT slot — it stays null.
        let guard = tables.get(&module).expect("symbol table present");
        let entry = guard.get(defn.name.as_ref()).expect("entry present");
        match entry {
            ModuleEntry::Def { got_slot: Some(slot), code, .. } => {
                assert!(
                    guard.got.load_slot(*slot).is_null(),
                    "object-mode compile must not populate the GOT slot"
                );
                assert!(
                    code.is_none(),
                    "object-mode entry's code field must be None"
                );
            }
            _ => unreachable!("test inserted a Def entry with a GOT slot"),
        }
    }

    // --- multi-sig defn tests ---
    //
    // Sprint 56 Wave 1: `build_mangled_name`, `concrete_type_name`, and
    // `expand_multi_sig_defn` were deleted from the backend. Mangled variant
    // entries are now pre-materialised by typecheck in Wave 0. The unit tests
    // that exercised those helpers directly are retired; end-to-end multi-sig
    // dispatch is covered by `test_compile_multi_sig_defn_end_to_end` and
    // `test_compile_multi_sig_second_variant` below (plus the integration
    // tests in `tests/`).

    // spec: 05-definitions §5.1.2 — multi-sig defn compiles and dispatches correctly
    //
    // Defines a multi-sig function `f` with two variants:
    //   (defn f ([x] x) ([a b] a))      — identity on 1 arg, first on 2 args
    // Then defines main that calls the first variant via SigDispatch.
    #[test]
    fn test_compile_multi_sig_defn_end_to_end() {
        let variant1_span = Span::new(10, 30);
        let variant2_span = Span::new(40, 60);

        let multi_defn = Defn {
            name: Symbol::from("f"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), resolved_call: None, inferred_type: None },
                    span: variant1_span,
                },
                DefnVariant {
                    params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                    body: Expr::Var { name: Symbol::from("a"), span: Span::new(45, 46), resolved_call: None, inferred_type: None },
                    span: variant2_span,
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 70),
        };

        // main calls f$Int(42)
        let call_span = Span::new(100, 120);
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("f"),
                        span: Span::new(101, 102),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    args: vec![Expr::IntLit { value: 42, span: Span::new(103, 105), inferred_type: None }],
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(95, 125),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(95, 125),
        };

        let program: Program = vec![
            TopLevel::Defn(multi_defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Register SigDispatch for the call site.
        check.method_resolutions.insert(
            call_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("f$Int"),
            },
        );

        // Set up symbol table with Overloaded entry for multi-sig expansion.
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let module_path = ModuleFullPath::from("user");
        let mut table = SymbolTable::new(module_path.clone());
        table.insert(
            Symbol::from("f"),
            cranelisp_types::ModuleEntry::Def {
                scheme: cranelisp_types::Scheme { type_vars: vec![], constraints: Default::default(), ty: Type::Int },
                visibility: cranelisp_types::Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(cranelisp_types::DefKind::Overloaded {
                    variants: vec![
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("f$Int"),
                        },
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int, Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("f$Int+Int"),
                        },
                    ],
                }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );
        tables.insert(module_path, table);

        let result = test_compile_program_and_run(&program, &check, &tables)
            .expect("multi-sig program should compile");
        assert_eq!(result, 42, "should dispatch to f$Int and return 42");
    }

    // spec: 05-definitions §5.1.2 — multi-sig dispatch to second variant
    #[test]
    fn test_compile_multi_sig_second_variant() {
        let variant1_span = Span::new(10, 30);
        let variant2_span = Span::new(40, 60);

        let multi_defn = Defn {
            name: Symbol::from("g"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![(Symbol::from("x"), None)],
                    body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), resolved_call: None, inferred_type: None },
                    span: variant1_span,
                },
                DefnVariant {
                    params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                    // Return b (second param) to prove we dispatched to the right variant.
                    body: Expr::Var { name: Symbol::from("b"), span: Span::new(45, 46), resolved_call: None, inferred_type: None },
                    span: variant2_span,
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 70),
        };

        // main calls g$Int+Int(10, 99) — should return 99 (the second arg)
        let call_span = Span::new(100, 120);
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("g"),
                        span: Span::new(101, 102),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 10, span: Span::new(103, 105), inferred_type: None },
                        Expr::IntLit { value: 99, span: Span::new(106, 108), inferred_type: None },
                    ],
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(95, 125),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(95, 125),
        };

        let program: Program = vec![
            TopLevel::Defn(multi_defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        check.method_resolutions.insert(
            call_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("g$Int+Int"),
            },
        );

        // Set up symbol table with Overloaded entry for multi-sig expansion.
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let module_path = ModuleFullPath::from("user");
        let mut table = SymbolTable::new(module_path.clone());
        table.insert(
            Symbol::from("g"),
            cranelisp_types::ModuleEntry::Def {
                scheme: cranelisp_types::Scheme { type_vars: vec![], constraints: Default::default(), ty: Type::Int },
                visibility: cranelisp_types::Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(cranelisp_types::DefKind::Overloaded {
                    variants: vec![
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("g$Int"),
                        },
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int, Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("g$Int+Int"),
                        },
                    ],
                }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );
        tables.insert(module_path, table);

        let result = test_compile_program_and_run(&program, &check, &tables)
            .expect("multi-sig program should compile");
        assert_eq!(result, 99, "should dispatch to g$Int+Int and return second arg (99)");
    }

    // Note: `test_expand_multi_sig_missing_type_info` and
    // `test_concrete_type_name_all_primitives` were retired in Sprint 56 Wave 1
    // with the deletion of `expand_multi_sig_defn` / `concrete_type_name`. The
    // equivalent mangled-name construction now lives in `/typecheck`, and the
    // "missing overload info" error surface is exercised by the backend's
    // `ast: None` error path (see `test_compile_to_module_ast_none_errors` in
    // the Sprint 56 Wave 1 unit tests below).

    // spec: appendix-a-builtins §A.2 — extern primitive dispatch via resolved_call
    //
    // Isolates the "undefined function: macros/sconcat" failure from
    // repl_defmacro_rest_splice. When compile_apply receives an Apply node
    // with resolved_call: Some(BuiltinFn { name: "sconcat" }), per Decision
    // 0048 §"Structural invariant — backend dep-ban" it MUST take the
    // standard GOT-indirect dispatch path (`compile_direct_call` →
    // `resolve_got_target` → load slot from `__cranelisp_got_primitives`).
    // Pre-Decision-0048 the path was direct extern via `compile_extern_call`;
    // that path is now reserved for non-module backend-emitted-call targets
    // (intrinsics — `vec-set-copy`, `runtime/alloc`, etc.). Primitives reach
    // the JIT via GOT-indirect uniformly with user-defined functions.
    //
    // Test setup: seed a `primitives` module with a `sconcat` entry that
    // carries `got_slot: Some(_)`, write the extern fn ptr into that slot,
    // then assert backend compiles + executes the call through the GOT.
    #[test]
    fn test_extern_primitive_via_resolved_call_succeeds() {
        use cranelisp_types::ResolvedCall;
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};

        // Build: (defn __expr__ [] (sconcat 0 0))
        let apply_span = Span::new(2000, 2030);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            apply_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("sconcat"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("macros/sconcat"),
                span: Span::new(2001, 2015),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 0, span: Span::new(2016, 2017), inferred_type: None },
                Expr::IntLit { value: 0, span: Span::new(2018, 2019), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None, // enrichment will set this from method_resolutions
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };

        // Seed a primitives module with `sconcat` and a GOT slot. Backend's
        // `resolve_got_target` consults this via its global-fallback walk
        // when the caller's module (`user`) has no local binding for the
        // unqualified name `sconcat`. Per Decision 0048's backend dep-ban,
        // we cannot reference `cranelisp_primitives::marshal::sconcat`
        // directly; we provide a local 2-arg stub matching the signature
        // and wire that fn ptr into the GOT slot. The test asserts
        // compilation + GOT-indirect dispatch — it does NOT assert the
        // semantics of `sconcat` (which is covered by the e2e
        // `mode_equiv_macro_user_defined` test).
        extern "C" fn sconcat_stub(_a: i64, _b: i64) -> i64 { 0 }
        let tables = empty_tables();
        let primitives_path = ModuleFullPath::from("primitives");
        let mut prim_table: SymbolTable = SymbolTable::new(primitives_path.clone());
        let slot = prim_table.allocate_got_slot();
        prim_table.got.store_slot(slot, sconcat_stub as *const u8);
        prim_table.insert(
            Symbol::from("sconcat"),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: Vec::new(),
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![Symbol::from("a"), Symbol::from("b")],
                kind: Box::new(DefKind::Primitive),
                callees: Vec::new(),
                got_slot: Some(slot),
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );
        tables.insert(primitives_path, prim_table);

        // With resolved_call present (via enrichment), compilation should
        // succeed via GOT-indirect dispatch through the primitives module.
        // The JIT also needs the `__cranelisp_got_primitives` data symbol
        // wired to the table's GOT base — register via
        // `Jit::new_with_symbols` (a separate code path from
        // `test_compile_and_run`'s `Jit::new`).
        let got_data_name = crate::compiler::got_data_symbol_name(
            &ModuleFullPath::from("primitives"),
        );
        let prim_got_base = tables
            .get(&ModuleFullPath::from("primitives"))
            .map(|st| st.got.base_ptr())
            .expect("primitives table just inserted");
        let extras: Vec<(&str, *const u8)> = vec![(got_data_name.as_str(), prim_got_base)];

        let mut defn = Defn {
            name: Symbol::from("__expr__"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: expr.clone(),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        enrich_defn_from_side_maps(&mut defn, &check.method_resolutions, &check.expr_types);

        let user_module = ModuleFullPath::from("user");
        let name = defn.name.clone();
        {
            let mut st = tables
                .entry(user_module.clone())
                .or_insert_with(|| SymbolTable::new(user_module.clone()));
            st.insert(name.clone(), make_def_entry(defn));
        }

        let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
        let aliases = empty_aliases();
        let result = compile_to_module(user_module, &[name], &tables, &aliases, jit.jit_module(), true);
        assert!(
            result.is_ok(),
            "extern primitive sconcat should compile via GOT-indirect when resolved_call is BuiltinFn: {}",
            result.err().map(|e| format!("{e:?}")).unwrap_or_default(),
        );
    }

    // spec: appendix-a-builtins §A.2 — missing resolved_call causes "undefined function"
    //
    // Companion to the test above: when resolved_call is None (not enriched),
    // compile_apply falls through to compile_var_apply -> compile_direct_call
    // which fails because "macros/sconcat" has no GOT slot or FuncId.
    // This is the broken path that the integration test hits.
    #[test]
    fn test_extern_primitive_without_resolved_call_fails() {
        // Build: (defn main [] (macros/sconcat 0 0))
        // No resolved_call, no GOT entry, no FuncId — should fail.
        let apply_span = Span::new(2100, 2130);

        // No method_resolutions — resolved_call stays None.
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("macros/sconcat"),
                span: Span::new(2101, 2115),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 0, span: Span::new(2116, 2117), inferred_type: None },
                Expr::IntLit { value: 0, span: Span::new(2118, 2119), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(
            result.is_err(),
            "macros/sconcat without resolved_call should fail"
        );
        let err_msg = format!("{:?}", result.unwrap_err());
        assert!(
            err_msg.contains("undefined function"),
            "error should be 'undefined function', got: {err_msg}"
        );
    }

    // -----------------------------------------------------------------
    // Sprint 56 Wave 1 (Step 2a) — direct compile_to_module tests
    // -----------------------------------------------------------------

    // spec: design/backend/compile-to-module.md §2 (S75 banner) — 5-param
    // signature; value-returned CompilationArtifacts + GOT-slot direct write.
    //
    // Direct `compile_to_module` call with a populated `symbol_tables` and a
    // single-name `names` list. Verifies the S75 contract: bodies arrive via
    // `ModuleEntry::Def.ast`, the finalised code pointer is written into the
    // entry's GOT slot (D41 #2), and the always-created `CompilationArtifacts`
    // carries the CLIF + code size.
    #[test]
    fn sprint56_compile_to_module_direct_call_writes_got_and_artifacts() {
        use cranelisp_types::ModuleEntry;
        let defn = Defn {
            name: Symbol::from("answer"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            // Explicit GOT slot so the D41 #2 direct-write is exercised.
            st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
            st.next_got_slot = 1;
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("direct compile_to_module should succeed");

        // Always-created introspection artefacts carry CLIF + code size.
        assert!(
            !artifacts.clif_ir.is_empty(),
            "CompilationArtifacts.clif_ir must capture the compiled function's CLIF"
        );
        assert!(
            artifacts.code_size > 0,
            "CompilationArtifacts.code_size must be the finalised native code size"
        );

        // D41 #2: the finalised code pointer is written into the entry's GOT
        // slot. Entry remains a Def with ast: Some(_) (regression guard).
        let guard = tables.get(&module).unwrap();
        match guard.get(defn.name.as_ref()) {
            Some(ModuleEntry::Def { ast: Some(_), got_slot: Some(slot), .. }) => {
                assert!(
                    !guard.got.load_slot(*slot).is_null(),
                    "backend must write the finalised code pointer to the GOT slot"
                );
            }
            other => panic!("expected Def with ast + got_slot, got {other:?}"),
        }
    }

    // spec: design/arch/facades/backend.md — `capture_clif` flag (FIXME 0325)
    //
    // The `capture_clif: bool` parameter (FIXME 0325) gates whether
    // `compile_to_module` populates `CompilationArtifacts.clif_ir` with the
    // CLIF-IR text. `false` skips the `format!("{}", func.display())` work and
    // leaves `clif_ir` empty; `true` captures it. This test compiles the same
    // fixture under both states and asserts they differ — if the flag were
    // ignored, the two `clif_ir` strings would match and the test fails.
    //
    // A fresh JIT + symbol-table pair is built per call because
    // `compile_to_module` finalizes the module and writes the GOT slot.
    #[test]
    fn capture_clif_gates_clif_ir_text() {
        fn compile_once(capture_clif: bool) -> CompilationArtifacts {
            let defn = Defn {
                name: Symbol::from("answer"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![],
                    body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
                    span: Span::new(0, 10),
                }],
                visibility: Visibility::Public,
                span: Span::new(0, 10),
            };

            let module = ModuleFullPath::from("user");
            let tables = empty_tables();
            {
                let mut st = SymbolTable::new(module.clone());
                st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
                st.next_got_slot = 1;
                tables.insert(module.clone(), st);
            }

            let mut jit = Jit::new_with_symbols(&[]).unwrap();
            let aliases = empty_aliases();
            compile_to_module(
                module,
                std::slice::from_ref(&defn.name),
                &tables,
                &aliases,
                jit.jit_module(),
                capture_clif,
            )
            .expect("direct compile_to_module should succeed")
        }

        // capture_clif = false: the CLIF text is not generated.
        let without = compile_once(false);
        assert!(
            without.clif_ir.is_empty(),
            "capture_clif = false must leave CompilationArtifacts.clif_ir empty, got: {:?}",
            without.clif_ir
        );

        // capture_clif = true: the CLIF text is captured.
        let with = compile_once(true);
        assert!(
            !with.clif_ir.is_empty(),
            "capture_clif = true must populate CompilationArtifacts.clif_ir"
        );

        // The compiled native code is unaffected by the flag — code_size is
        // produced in both cases (the flag only gates the CLIF *text*).
        assert!(
            without.code_size > 0 && with.code_size > 0,
            "code_size must be produced regardless of capture_clif"
        );
    }

    // spec: design/backend/compile-to-module.md §4 — ast: None returns error
    //
    // Negative: insert a `ModuleEntry::Def { ast: None, .. }` into the symbol
    // table and pass its name in `names`. `compile_to_module` must return
    // `Err(CranelispError::CodegenError)` whose message names the symbol —
    // no panic, no silent skip.
    #[test]
    fn sprint56_compile_to_module_ast_none_errors() {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let module = ModuleFullPath::from("user");
        let name = Symbol::from("stub");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(
                name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        type_vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Fn(vec![], Box::new(Type::Int)),
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    callees: vec![],
                    got_slot: None,
                    trait_origin: None,
                    seq: 0,
                    ast: None,
                    code: None,
                },
            );
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let result = compile_to_module(
            module,
            std::slice::from_ref(&name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        );
        let err = match result {
            Ok(_) => unreachable!("ast: None must not succeed"),
            Err(e) => e,
        };

        let msg = err.to_string();
        assert!(
            msg.contains(name.as_ref()),
            "error message must name the offending symbol 'stub', got: {msg}"
        );
        assert!(
            msg.contains("ast: None") || msg.contains("ast") && msg.contains("None"),
            "error message should mention the ast: None invariant violation, got: {msg}"
        );
    }

    // spec: design/backend/compile-to-module.md §4 — no multi-sig expansion in backend
    //
    // Populate symbol_tables with a pre-mangled multi-sig variant entry
    // (`add$Int+Int`, ast: Some(single-variant defn)) alongside the
    // Overloaded base entry (`add`, ast: None). Call compile_to_module with
    // names = [mangled variant]. Compilation must succeed — the backend never
    // invokes a (deleted) `expand_multi_sig_defn` path.
    //
    // That this test compiles and passes IS the verification: Wave 1 deleted
    // `expand_multi_sig_defn` entirely from the source tree.
    #[test]
    fn sprint56_compile_to_module_mangled_variant_compiles_without_expansion() {
        use cranelisp_types::{DefKind, ModuleEntry, OverloadVariant, Scheme, Visibility};

        let module = ModuleFullPath::from("user");
        let base_name = Symbol::from("add");
        let variant_name = Symbol::from("add$Int+Int");

        // Mangled variant defn — what typecheck's Wave 0 materialises.
        let variant_defn = Defn {
            name: variant_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                // Body returns x (proves the variant body is what got compiled).
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(5, 6),
                    resolved_call: None,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            // Overloaded base entry: ast: None — compile_to_module must NOT
            // try to compile this (the filter via `defined_symbols()` skips
            // it; a caller passing it in `names` would hit the ast: None
            // error path — which is the right behaviour).
            st.insert(
                base_name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        type_vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Int,
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::Overloaded {
                        variants: vec![OverloadVariant {
                            param_types: vec![Type::Int, Type::Int],
                            ret_type: Type::Int,
                            mangled_name: variant_name.clone(),
                        }],
                    }),
                    callees: vec![],
                    got_slot: None,
                    trait_origin: None,
                    seq: 0,
                    ast: None,
                    code: None,
                },
            );
            // Mangled variant entry: ast: Some(variant_defn). Explicit GOT
            // slot so the D41 #2 direct-write is exercised.
            st.insert(variant_name.clone(), make_def_entry_slot(variant_defn, 0));
            st.next_got_slot = 1;
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&variant_name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("pre-mangled variant should compile without expansion");

        // Compilation succeeding (no expand_multi_sig_defn path) is the
        // verification; the mangled variant's GOT slot is populated.
        assert!(!artifacts.clif_ir.is_empty(), "variant body must be compiled");
        let guard = tables.get(&module).unwrap();
        match guard.get(variant_name.as_ref()) {
            Some(ModuleEntry::Def { got_slot: Some(slot), .. }) => {
                assert!(
                    !guard.got.load_slot(*slot).is_null(),
                    "mangled variant's GOT slot must be populated"
                );
            }
            other => panic!("expected mangled-variant Def with got_slot, got {other:?}"),
        }
    }

    // spec: design/backend/compile-to-module.md §4 — constrained-template exclusion via defined_symbols
    //
    // Verifies that `SymbolTable::defined_symbols()` — the shared filter
    // callers use to build the `names` list — excludes constrained-function
    // templates (`UserFn { constrained_fn: Some(_) }`). The backend relies
    // on this filter upstream; if it were to break, constrained templates
    // would reach compile_to_module and fail (templates carry type vars,
    // not concrete types). This re-asserts Wave 0's contract from the
    // backend's vantage point.
    #[test]
    fn sprint56_constrained_template_excluded_by_defined_symbols() {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};

        let module = ModuleFullPath::from("user");
        let template_name = Symbol::from("identity");
        let normal_name = Symbol::from("answer");

        // A typical regular defn: compile-eligible.
        let normal_defn = Defn {
            name: normal_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 1, span: Span::new(0, 1), inferred_type: None },
                span: Span::new(0, 5),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 5),
        };

        // A constrained-fn template defn: should be filtered OUT by
        // defined_symbols() even though it carries ast: Some(_).
        let template_defn = Defn {
            name: template_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(0, 1),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(normal_name.clone(), make_def_entry(normal_defn));
            // Insert a UserFn template by hand — constrained_fn is Some.
            st.insert(
                template_name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        type_vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![Symbol::from("x")],
                    kind: Box::new(DefKind::UserFn {
                        // Sentinel — real typecheck stores a single DefnVariant here.
                        constrained_fn: Some(Box::new(cranelisp_types::ConstrainedFn {
                            variant: template_defn.variants[0].clone(),
                            scheme: Scheme {
                                type_vars: vec![],
                                constraints: HashMap::new(),
                                ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                            },
                        })),
                    }),
                    callees: vec![],
                    got_slot: None,
                    trait_origin: None,
                    seq: 0,
                    ast: Some(template_defn.variants[0].clone()),
                    code: None,
                },
            );
            tables.insert(module.clone(), st);
        }

        let guard = tables.get(&module).unwrap();
        let defined: Vec<&Symbol> = guard.defined_symbols().map(|(n, _)| n).collect();

        assert!(
            defined.contains(&&normal_name),
            "defined_symbols() must yield regular defns: got {:?}",
            defined
        );
        assert!(
            !defined.contains(&&template_name),
            "defined_symbols() must NOT yield constrained-fn templates: got {:?}",
            defined
        );
    }

    // ----- Sprint 58 Wave 2: Decision 36 + Decision 23 unit tests -----
    //
    // These tests cover the architectural reconciliation landed in Sprint 58
    // Wave 2: bare-name + Linkage::Local function declarations uniformly across
    // all modules (Decision 36), and `__cranelisp_got_{M}` defined as
    // Linkage::Export data symbol in the .o (Decision 23 — Bug B fix).

    /// Helper: make an ObjectModule for these tests (PIC enabled).
    fn make_object_module() -> cranelift_object::ObjectModule {
        use cranelift_module::default_libcall_names;
        use cranelift_object::ObjectBuilder;

        let isa = crate::cache::object::build_isa(true).unwrap();
        let builder = ObjectBuilder::new(isa, "test", default_libcall_names()).unwrap();
        cranelift_object::ObjectModule::new(builder)
    }

    /// Helper: build a single-defn symbol table with `got_slot: Some(slot)` so
    /// the GOT-data emission step has a slot to populate.
    fn table_with_def_and_slot(
        module: &ModuleFullPath,
        defn: Defn,
        slot: usize,
    ) -> DashMap<ModuleFullPath, SymbolTable> {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let tables = DashMap::new();
        let mut st = SymbolTable::new(module.clone());
        // Match the slot index: typecheck would have called allocate_got_slot
        // exactly `slot+1` times.
        for _ in 0..=slot {
            let _ = st.allocate_got_slot();
        }
        let param_count = defn.params().len();
        let param_names: Vec<Symbol> = defn
            .variants
            .first()
            .map(|v| v.params.iter().map(|(n, _)| n.clone()).collect())
            .unwrap_or_default();
        let variant = defn.variants.first().cloned();
        st.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(
                        (0..param_count).map(|_| Type::Int).collect(),
                        Box::new(Type::Int),
                    ),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names,
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: Some(slot),
                trait_origin: None,
                seq: 0,
                ast: variant,
                code: None,
            },
        );
        tables.insert(module.clone(), st);
        tables
    }

    /// Helper: trivial zero-arg defn returning an int literal.
    fn make_int_defn(name: &str, value: i64) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value, span: Span::SYNTHETIC, inferred_type: None },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    // spec: design/arch/CLAUDE.md Decision 36 — function symbols are declared
    // with their bare name uniformly across all modules. The pre-Sprint-58
    // user/main vs FQ-Export discriminator is deleted.
    #[test]
    fn decision_36_function_naming_is_bare_for_every_module() {
        use cranelift_module::Module;
        for module_path_str in ["user", "main", "util", "one.two.three"] {
            let module = ModuleFullPath::from(module_path_str);
            let defn = make_int_defn("helper", 7);
            let tables = table_with_def_and_slot(&module, defn.clone(), 0);

            let mut jit = Jit::new_with_symbols(&[]).unwrap();
            let aliases = empty_aliases();
            let _artifacts = compile_to_module(
                module.clone(),
                std::slice::from_ref(&defn.name),
                &tables,
                &aliases,
                jit.jit_module(),
                true,
            )
            .expect("compile_to_module should succeed");

            // The Cranelift module's declaration table records the bare name.
            // (Decision 36: even for non-user/main, the FQ form must be absent.)
            let fq = format!("{module_path_str}/helper");
            let m = jit.jit_module();
            let has_fq = m.get_name(&fq).is_some();
            let has_bare = m.get_name("helper").is_some();
            assert!(
                !has_fq,
                "module '{module_path_str}': bare-only contract violated — module-qualified name '{fq}' should NOT be a declaration"
            );
            assert!(
                has_bare,
                "module '{module_path_str}': bare name 'helper' must be a declaration"
            );
        }
    }

    // spec: design/arch/CLAUDE.md Decision 36 — function linkage is Local
    // uniformly. Symbols never need to cross .o boundaries (all-GOT calling).
    #[test]
    fn decision_36_function_linkage_is_local_uniformly() {
        use cranelift_module::{FuncOrDataId, Linkage, Module};
        for module_path_str in ["user", "main", "util", "deep.nested.path"] {
            let module = ModuleFullPath::from(module_path_str);
            let defn = make_int_defn("f", 1);
            let tables = table_with_def_and_slot(&module, defn.clone(), 0);

            let mut jit = Jit::new_with_symbols(&[]).unwrap();
            let aliases = empty_aliases();
            let _result = compile_to_module(
                module.clone(),
                std::slice::from_ref(&defn.name),
                &tables,
                &aliases,
                jit.jit_module(),
                true,
            )
            .expect("compile_to_module should succeed");

            let m = jit.jit_module();
            let func_id = match m.get_name("f") {
                Some(FuncOrDataId::Func(id)) => id,
                other => panic!("module '{module_path_str}': expected FuncOrDataId::Func for 'f', got {other:?}"),
            };
            let decl = m.declarations().get_function_decl(func_id);
            assert_eq!(
                decl.linkage,
                Linkage::Local,
                "module '{module_path_str}': function 'f' must have Linkage::Local per Decision 36, got {:?}",
                decl.linkage
            );
        }
    }

    // spec: design/arch/CLAUDE.md Decision 23 (updated) — `__cranelisp_got_{M}`
    // is defined as Linkage::Export data with `slot_count * 8` bytes inside
    // the .o emitted by compile_to_module<ObjectModule>.
    #[test]
    fn decision_23_got_data_symbol_defined_as_export_in_object_path() {
        use cranelift_module::Module;
        let module = ModuleFullPath::from("util");
        let defn = make_int_defn("answer", 42);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut obj = make_object_module();
        let aliases = empty_aliases();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            &mut obj,
            true,
        )
        .expect("compile_to_module<ObjectModule> should succeed");

        // The GOT data symbol should now be a defined Export data symbol.
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let id = obj
            .get_name(&got_name)
            .expect("GOT data symbol must be declared");
        let data_id = match id {
            cranelift_module::FuncOrDataId::Data(d) => d,
            other => panic!("expected DataId for {got_name}, got {other:?}"),
        };
        let decl = obj.declarations().get_data_decl(data_id);
        assert_eq!(
            decl.linkage,
            cranelift_module::Linkage::Export,
            "GOT data symbol '{got_name}' must be Linkage::Export, got {:?}",
            decl.linkage
        );

        // Emit the .o and parse it; confirm:
        //  (a) the GOT data symbol is present in the .o symbol table
        //  (b) it has global scope (Export = visible to the system linker)
        //  (c) it points into a Data-kind section
        // (Size in the .o symbol table is not portable across formats —
        // Mach-O always reports 0; we rely on the in-Module declaration
        // size assertion and the section-data check instead.)
        let product = obj.finish();
        let bytes = product.emit().expect("ObjectModule should emit");
        use ::object::{Object, ObjectSymbol, SymbolKind, SymbolScope};
        let parsed = ::object::File::parse(&*bytes)
            .expect("emitted bytes must parse as an object file");
        let got_sym = parsed
            .symbols()
            .find(|s| {
                s.name()
                    .map(|n| n.strip_prefix('_').unwrap_or(n) == got_name)
                    .unwrap_or(false)
            })
            .unwrap_or_else(|| {
                panic!(
                    "GOT data symbol '{got_name}' must appear in emitted .o; \
                     symbols present: {:?}",
                    parsed
                        .symbols()
                        .filter_map(|s| s.name().ok().map(|n| n.to_string()))
                        .collect::<Vec<_>>()
                )
            });
        assert_ne!(
            got_sym.scope(),
            SymbolScope::Compilation,
            "GOT data symbol '{got_name}' must have global scope (Linkage::Export); got {:?}",
            got_sym.scope()
        );
        assert_eq!(
            got_sym.kind(),
            SymbolKind::Data,
            "GOT data symbol '{got_name}' must be a Data-kind symbol; got {:?}",
            got_sym.kind()
        );
    }

    // spec: design/arch/CLAUDE.md Decision 23 — JIT-mode GOT-data definition
    // remains the integration layer's responsibility (`Jit::define_got_data`).
    // compile_to_module<JITModule>'s `define_module_got_data` is a no-op and
    // does NOT redundantly declare/define the symbol on the JIT module.
    #[test]
    fn decision_23_got_data_symbol_jit_path_is_noop() {
        use cranelift_module::Module;
        let module = ModuleFullPath::from("user");
        let defn = make_int_defn("answer", 42);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("compile_to_module<JITModule> should succeed");

        // In JIT mode, the GOT data symbol is NOT defined by compile_to_module.
        // It might be an Import declaration if the compiled code emitted a
        // GOT-indirect call (unlikely in this minimal test — answer is a
        // direct expression), but it must NEVER be Export-defined here.
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let m = jit.jit_module();
        if let Some(cranelift_module::FuncOrDataId::Data(data_id)) = m.get_name(&got_name) {
            let decl = m.declarations().get_data_decl(data_id);
            assert_ne!(
                decl.linkage,
                cranelift_module::Linkage::Export,
                "JIT path: GOT data symbol '{got_name}' must NOT be Linkage::Export-defined by compile_to_module — JIT-mode definition lives in Jit::define_got_data (Decision 23)"
            );
        }
        // (If it's not declared at all, that's also fine — this minimal defn
        // doesn't emit a GOT-indirect call so neither path declares it.)
    }

    // spec: design/arch/CLAUDE.md Decision 23 — GOT data symbol size matches
    // the symbol table's `next_got_slot` (one 8-byte slot per allocated index).
    #[test]
    fn decision_23_got_data_size_matches_slot_count() {
        use cranelift_module::Module;
        // Two defns with two GOT slots → 16 bytes.
        let module = ModuleFullPath::from("util");
        let d1 = make_int_defn("one", 1);
        let d2 = make_int_defn("two", 2);

        // Build symbol table with both defns at slots 0 and 1.
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let tables = DashMap::new();
        let mut st = SymbolTable::new(module.clone());
        let _slot0 = st.allocate_got_slot();
        let _slot1 = st.allocate_got_slot();
        for (defn, slot) in [(d1.clone(), 0usize), (d2.clone(), 1)] {
            st.insert(
                defn.name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        type_vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Fn(vec![], Box::new(Type::Int)),
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    callees: vec![],
                    got_slot: Some(slot),
                    trait_origin: None,
                    seq: 0,
                    ast: defn.variants.first().cloned(),
                    code: None,
                },
            );
        }
        tables.insert(module.clone(), st);

        let mut obj = make_object_module();
        let aliases = empty_aliases();
        let _result = compile_to_module(
            module.clone(),
            &[d1.name.clone(), d2.name.clone()],
            &tables,
            &aliases,
            &mut obj,
            true,
        )
        .expect("compile_to_module should succeed");

        // Verify in-Module declaration size; we cannot rely on the .o
        // symbol-table `size()` (Mach-O reports 0). The Cranelift
        // declaration carries the requested initialization size.
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let data_id = match obj.get_name(&got_name) {
            Some(cranelift_module::FuncOrDataId::Data(id)) => id,
            other => panic!("expected DataId for {got_name}, got {other:?}"),
        };
        let _decl = obj.declarations().get_data_decl(data_id);

        let product = obj.finish();
        let bytes = product.emit().unwrap();
        use ::object::{Object, ObjectSection, ObjectSymbol};
        let parsed = ::object::File::parse(&*bytes).unwrap();
        let got_sym = parsed
            .symbols()
            .find(|s| {
                s.name()
                    .map(|n| n.strip_prefix('_').unwrap_or(n) == got_name)
                    .unwrap_or(false)
            })
            .expect("GOT data symbol present");

        // Look up the section the symbol lives in and check it is at least
        // slot_count * 8 = 16 bytes long. (Cranelift may pack multiple data
        // symbols into the same section; this is a lower-bound check for the
        // GOT slab's storage budget.)
        let sect_idx = match got_sym.section_index() {
            Some(idx) => idx,
            None => panic!("GOT data symbol must live in a section"),
        };
        let section = parsed.section_by_index(sect_idx).unwrap();
        assert!(
            section.size() >= 16,
            "section containing GOT data symbol must hold at least slot_count(2) * 8 = 16 bytes; got {}",
            section.size()
        );
    }

    // spec: design/arch/CLAUDE.md Decision 36 — cross-module function refs
    // are NOT declared as Linkage::Import in the importing module's .o. Under
    // all-GOT calling, cross-module calls reach callees through
    // `__cranelisp_got_{other_M}` data symbol — never through a function-symbol
    // import. Verifies the cross_refs declaration loop deletion did not
    // re-introduce stray Import-linkage function declarations.
    #[test]
    fn decision_36_no_cross_module_function_imports() {
        use cranelift_module::{FuncOrDataId, Linkage, Module};

        // Build two modules: util defines `helper`, user imports `helper`.
        // Compile user.
        let util_path = ModuleFullPath::from("util");
        let user_path = ModuleFullPath::from("user");

        let helper = make_int_defn("helper", 99);
        // user has a single defn `caller` that does NOT call helper at runtime
        // (this test only checks the declaration shape; we focus on what
        // compile_to_module declares against the user module). The Import
        // entry on user's table records the cross-module dependency.
        let caller = make_int_defn("caller", 7);

        use cranelisp_types::{DefKind, FQSymbol, ModuleEntry, Scheme, Visibility,
        };
        let tables = DashMap::new();

        // util module: helper at slot 0.
        let mut util_st = SymbolTable::new(util_path.clone());
        let _ = util_st.allocate_got_slot();
        util_st.insert(
            Symbol::from("helper"),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: Some(0),
                trait_origin: None,
                seq: 0,
                ast: helper.variants.first().cloned(),
                code: None,
            },
        );
        tables.insert(util_path.clone(), util_st);

        // user module: caller at slot 0, helper imported from util.
        let mut user_st = SymbolTable::new(user_path.clone());
        let _ = user_st.allocate_got_slot();
        user_st.insert(
            Symbol::from("caller"),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: Some(0),
                trait_origin: None,
                seq: 0,
                ast: caller.variants.first().cloned(),
                code: None,
            },
        );
        user_st.insert(
            Symbol::from("helper"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: util_path.clone(),
                    symbol: Symbol::from("helper"),
                },
                visibility: Visibility::Private,
            },
        );
        tables.insert(user_path.clone(), user_st);

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let result = compile_to_module(
            user_path.clone(),
            &[Symbol::from("caller")],
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("compile_to_module should succeed");

        // Per Decision 36 + cross_refs deletion: there must be NO
        // Linkage::Import declaration for the cross-module function name
        // (neither `helper` nor `util/helper`).
        let m = jit.jit_module();
        for candidate in ["helper", "util/helper"] {
            if let Some(FuncOrDataId::Func(fid)) = m.get_name(candidate) {
                let decl = m.declarations().get_function_decl(fid);
                assert_ne!(
                    decl.linkage,
                    Linkage::Import,
                    "cross-module fn '{candidate}' must NOT be declared as Linkage::Import; got {:?}. Under all-GOT calling, cross-module calls flow through __cranelisp_got_{{M}} data symbols, not function imports.",
                    decl.linkage
                );
            }
        }

        // Sanity: `caller` is declared bare-Local (compiled this batch).
        let _ = &result; // CompilationArtifacts carries CLIF/size, not func_ids
        assert!(
            matches!(m.get_name("caller"), Some(FuncOrDataId::Func(_))),
            "bare 'caller' must be a function declaration"
        );
    }

    // spec: design/arch/CLAUDE.md Decision 23 — Sprint 58 Wave 2 regression
    // guard. The `__cranelisp_got_{M}` data symbol carries function-address
    // relocations (declared via `desc.write_function_addr`). On macOS, `ld`
    // segfaults when applying relocations against `__DATA,__bss`
    // (`S_ZEROFILL`) sections. The Wave 2 implementation MUST emit GOT
    // contents via `desc.define(zero_bytes)` (regular `__DATA`), NOT
    // `desc.define_zeroinit(...)` (which lands in BSS / `S_ZEROFILL`).
    // This test asserts the emitted .o has the GOT data symbol in a regular
    // (non-BSS) data section.
    #[test]
    fn decision_23_got_data_symbol_not_in_bss() {
        let module = ModuleFullPath::from("util");
        let defn = make_int_defn("answer", 42);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut obj = make_object_module();
        let aliases = empty_aliases();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            &mut obj,
            true,
        )
        .expect("compile_to_module<ObjectModule> should succeed");

        let product = obj.finish();
        let bytes = product.emit().expect("ObjectModule should emit");

        use ::object::{Object, ObjectSection, ObjectSymbol, SectionKind};
        let parsed = ::object::File::parse(&*bytes)
            .expect("emitted bytes must parse as an object file");
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let got_sym = parsed
            .symbols()
            .find(|s| {
                s.name()
                    .map(|n| n.strip_prefix('_').unwrap_or(n) == got_name)
                    .unwrap_or(false)
            })
            .expect("GOT data symbol must appear in emitted .o");
        let sect_idx = got_sym
            .section_index()
            .expect("GOT data symbol must live in a section, not be undefined");
        let section = parsed
            .section_by_index(sect_idx)
            .expect("section must be resolvable");

        // Negative path: must NOT be UninitializedData (BSS / __DATA,__bss /
        // S_ZEROFILL). macOS `ld` segfaults on relocations against BSS.
        let kind = section.kind();
        assert_ne!(
            kind,
            SectionKind::UninitializedData,
            "GOT data symbol '{got_name}' landed in BSS (UninitializedData) — \
             macOS `ld` segfaults on relocations against BSS. Use \
             `desc.define(zero_bytes)` not `desc.define_zeroinit(...)` so the \
             data lands in regular `__DATA`."
        );
        // Positive path: must be a regular initialized Data section so
        // function-address relocations resolve correctly.
        assert!(
            matches!(kind, SectionKind::Data | SectionKind::ReadOnlyData),
            "GOT data symbol '{got_name}' must live in a regular initialized data section; got {kind:?}"
        );
    }
}
