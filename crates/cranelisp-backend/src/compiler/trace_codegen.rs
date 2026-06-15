//! Trace form codegen: `compile_trace` method for `FnCompiler`.
//!
//! Implements `(trace body)` -- a GOT-swap wrapper around a body expression,
//! returning a `Trace` ADT representing the call tree.
//!
//! # S76 target shape (FIXME 0255, `design/arch/tracing.md` §3.3–§3.4, §5)
//!
//! Three responsibilities landed here in S76:
//!
//! 1. **Discovery-in-codegen, swap ALL symbol tables** (`discover_traced_fns`).
//!    Backend computes the traced set itself by iterating every module's GOT in
//!    `symbol_tables` — no int-supplied `traced_fns`, no project-root filter,
//!    primitives included. The callable address is read from the **GOT slot**
//!    (BC §3 invariant 3 — the single source of truth), not from `entry.code`,
//!    so primitives (whose entries carry `code: None` but whose fn ptrs live in
//!    their module's GOT) are naturally included without a code-marker special
//!    case. Constrained-poly base names are skipped (dispatch placeholders).
//!
//! 2. **Display-descriptor baking** (`bake_descriptor_blob`). Each traced
//!    param/result type is baked into a self-contained position-independent
//!    **arena blob** matching the `DisplayDescriptor` ABI owned by
//!    `cranelisp-intrinsics::trace` (FIXME 0254). The blob replaces the leaked
//!    `Box<Type>` second arg to `cranelisp_trace_format`; the intrinsic walks it
//!    with zero symbol-table access. Polymorphic ADT fields are baked after
//!    substituting the call site's concrete type args (the same substitution
//!    `src/display.rs::build_adt_subst` does — replicated here, not imported).
//!
//! 3. **Both-modes emission.** The blob is emitted as a read-only data symbol
//!    via `declare_anonymous_data` + `define_data`, then its address is
//!    materialised inside the wrapper via `declare_data_in_func` + `global_value`.
//!    This single path is mode-agnostic: `JITModule` patches the `global_value`
//!    to a runtime address; `ObjectModule` emits one relocation per wrapper
//!    reference against the data symbol (same family as the GOT data symbol +
//!    string-literal pools). The blob itself carries NO intra-blob relocations —
//!    every cross-link is a self-relative `i32` byte offset — so it survives
//!    `.o` caching unchanged (`tracing.md` §3.4 "arena blob with offset-relative
//!    child links").
//!
//! # Nested-trace guard — no codegen touch-point
//!
//! Per the landed intrinsics guard design (`crates/cranelisp-intrinsics/src/trace.rs`
//! crate-doc §"The nested-trace runtime guard"), backend emits NO explicit
//! `TRACE_BODY_RUNNING` set/clear. The flag is driven entirely from inside the
//! intrinsic bodies backend already calls: `cranelisp_trace_enter` (the first
//! wrapper to fire) raises it, `cranelisp_collect_trace` clears it. Backend MUST
//! honour two constraints, both satisfied below:
//!   (a) it never clears `TRACE_BODY_RUNNING` itself (it emits no such call);
//!   (b) it emits `cranelisp_collect_trace` exactly once per `(trace ...)` form,
//!       as the LAST trace operation (see `compile_trace` / `compile_trace_no_swap`).
//!
//! The trace externs resolve from `cranelisp_intrinsics::catalog::intrinsics_table()`
//! in every mode (JIT `JITBuilder::symbol`, cache-hit `Linker::register_symbol`,
//! `--link` archive resolution) — backend just declares them `Linkage::Import`.
//!
//! # Object-mode relocation discipline — every baked address is a relocation (FIXME 0275)
//!
//! A linked binary runs in a DIFFERENT process from the compiler. Any
//! compiling-process absolute address baked as an `iconst` is garbage in the
//! target process — the original symptom was a `--link` binary containing
//! `(trace …)` SIGBUSing (exit 138). The fix: every address the trace machinery
//! needs is materialised through a **relocation**, identical in JIT and object
//! mode (no mode fork), via the `declare_data{,_in_func}` + `global_value`
//! family that `apply.rs::compile_direct_call` and the descriptor blob already
//! use. JIT patches the `global_value` to a runtime address; `ObjectModule`
//! emits one relocation per reference, resolved by `ld` at link time. The four
//! addresses and how each is now sourced:
//!
//! 1. **GOT base** (per traced group). Referenced via the module's GOT **data
//!    symbol** (`got_data_symbol_name`), declared `Linkage::Import` +
//!    `global_value` — never the stale `got_base` i64. Grouping is by
//!    `ModuleFullPath` (each module has its own GOT data symbol) rather than the
//!    raw base. Object-mode existence: every user/stdlib module compiled in
//!    this build emits its `__cranelisp_got_{M}` data symbol as
//!    `Linkage::Export` with per-slot function-address relocations
//!    (`define_module_got_data`), so referencing it as `Import` resolves at
//!    link time. The synthetic `primitives` module is NO LONGER an exception
//!    (FIXME 0280, S76 Wave 3): per Decision 0048 its GOT is still a static in
//!    `cranelisp-primitives` (`PRIMITIVES_TABLE`), but that static is now an
//!    EXPORTED writable slab (`PRIMITIVES_GOT_SLAB`,
//!    `#[unsafe(export_name = "__cranelisp_got_primitives")]`) over which the
//!    `GotTable` is constructed (`GotTable::with_static_backing`). In JIT/`--run`
//!    `__cranelisp_got_primitives` is registered as a JIT symbol (`jit.rs`
//!    registers ALL modules' GOT symbols incl. primitives); in object mode the
//!    exported static IS the link symbol, so the `Import` reference resolves at
//!    `ld` time exactly like any user/stdlib module's GOT. The primitives group
//!    swaps in ALL modes — extern primitives now appear in `--link` trace trees
//!    (only inline primitives `+`, `-`, … remain invisible in all modes).
//!
//! 2. **Original callee code ptr** (per traced fn). The wrapper must call the
//!    ORIGINAL, not the swapped slot (which now points at the wrapper →
//!    recursion). We do NOT bake `code_ptr`, and we do NOT `func_addr` against a
//!    per-callee linker symbol (cross-module + primitives have no in-`.o` symbol
//!    — their ptrs live only in the startup-populated GOT). Instead, uniformly:
//!    `compile_trace` loads `got_base[slot]` into a per-group **originals**
//!    buffer BEFORE the swap installs the wrappers (so the slot still holds the
//!    real fn), and each wrapper loads its original from `originals[i]`. This is
//!    the late-bound, mode-agnostic, BC §3-invariant-3-consistent choice (the
//!    GOT slot is the single source of truth for callable addresses) — one
//!    uniform path for user / stdlib / primitive callees alike.
//!
//! 3. **The slots / wrappers / originals / name buffers.** No leaked `Box`
//!    (compiling-process heap, garbage in the target). Emitted as data symbols:
//!    - *slots* — read-only, defined with the compile-time-constant u32 slot
//!      indices (`emit_ro_data`).
//!    - *wrappers* — WRITABLE (`emit_zero_data(writable=true)`): the wrapper
//!      func_addrs are stored at runtime; read by `swap_got`.
//!    - *originals* — WRITABLE: the pre-swap GOT-slot loads are stored at
//!      runtime; read by each wrapper.
//!    - *function name* — read-only bytes (`emit_ro_data`), referenced by the
//!      wrapper via `global_value` (passed to `cranelisp_trace_enter`).
//!
//!    For all of these, `define` with explicit zero bytes (not
//!    `define_zeroinit`) keeps the writable buffers in a regular `__DATA`
//!    section so macOS `ld` does not segfault applying relocations against a
//!    BSS atom (same rationale as `define_module_got_data`).
//!
//! 4. **No mode fork.** Every case above is a uniform relocation; JIT and object
//!    differ only in how Cranelift lowers `global_value` (movz/movk vs ADRP+ADD)
//!    and who resolves the symbol (JITModule patch vs `ld`). There is no
//!    JIT-only / object-only branch in this file.

use std::collections::HashMap;

use cranelift::codegen::ir::{StackSlotData, StackSlotKind};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_intrinsics::trace::DescriptorKind;
use cranelisp_types::{
    CranelispError, ErrorLocation, Expr, FQTypeName, ModuleEntry, Span, Type, TypeId,
};

use super::{FnCompiler, TracedFnInfo};

/// Maximum descriptor-tree depth. Recursive/cyclic ADT types (e.g.
/// `(deftype (List a) Nil (Cons [:a head :(List a) tail]))`) would otherwise
/// recurse without bound. Beyond this depth a node is degraded to a `TypeVar`
/// descriptor — the intrinsics walker renders it as the bare value, exactly the
/// residual-type-var fallback (`tracing.md` §3.4: the walker assumes a tree, so
/// backend bounds the depth and degrades interior repeats rather than emitting
/// an infinite blob). 16 is far beyond any realistic display nesting while
/// keeping a recursive `List`/`Tree` trace terminating.
const MAX_DESCRIPTOR_DEPTH: usize = 16;
// The bound must allow real display nesting (e.g. `(Option (Vec Int))` is 3
// levels) while keeping recursive ADTs terminating.
const _: () = assert!(MAX_DESCRIPTOR_DEPTH >= 4);

// ════════════════════════════════════════════════════════════════════════════
// Arena-blob builder — mirrors the `DisplayDescriptor` ABI (intrinsics-owned).
// ════════════════════════════════════════════════════════════════════════════
//
// Encoding (the single rule, from `cranelisp_intrinsics::trace::DisplayDescriptor`
// rustdoc): a contiguous `Vec<u8>` of fixed-size 24-byte descriptor records plus
// the variable-length data they reference (BlobStr, CtorTable). Every cross-link
// is a self-relative i32 byte offset measured from the offset field's own
// address; 0 = absent. No absolute pointers, no intra-blob relocations.

/// Record size in bytes — `size_of::<DisplayDescriptor>()`. Pinned by the
/// intrinsics `const _: assert!(size_of == 24)`; mirrored here as the stride.
const DESC_SIZE: usize = 24;
// Keep the arena stride in lockstep with the intrinsics-owned `DisplayDescriptor`
// ABI — a size change on either side fails this compile-time check (FIXME 0254/0255).
const _: () =
    assert!(DESC_SIZE == std::mem::size_of::<cranelisp_intrinsics::trace::DisplayDescriptor>());

// Field byte offsets within a descriptor record (see DisplayDescriptor rustdoc).
const OFF_KIND: usize = 0;
const OFF_NAME: usize = 8; // name_off (Adt type name)
const OFF_CHILD0: usize = 12; // child0_off (Vec element)
const OFF_CTORS: usize = 16; // ctors_off (Adt ctor table)

/// A flat position-independent descriptor arena.
struct DescriptorBlob {
    buf: Vec<u8>,
}

/// Per-blob descriptor-bake memo (FIXME 0340 timing fix).
///
/// `bake_descriptor` is structurally recursive over `Type`. Without memoization
/// a recursive or DAG-shaped ADT (e.g. the `Sexp`/`SList` mutual cycle used by
/// every macro-clause wrapper) is re-baked at every depth up to
/// `MAX_DESCRIPTOR_DEPTH`, which is **exponential** in the cycle's branching
/// factor — the dominant cost in `(trace …)` codegen (~1.3s per macro-clause
/// wrapper × ~170 discovered fns ≈ 30s+). The memo collapses the recursion to
/// **linear in the number of distinct types**:
///
/// - `done` records a fully-baked type → its blob offset. A second occurrence of
///   the same type reuses the offset (DAG sharing). Sharing is sound: the blob
///   only grows, so a baked record's offset is stable, and the formatter reads
///   descriptors immutably (a tree-walker over a shared-subtree DAG visits the
///   same record from several parents — read-only, no aliasing hazard).
/// - `in_progress` holds the types currently on the bake stack. A type that
///   recurses into ITSELF (a true cycle, e.g. `SList → Sexp → SList`) is degraded
///   to `TypeVar` (bare-value render) at the back-edge — the same termination the
///   `MAX_DESCRIPTOR_DEPTH` guard provided, but reached at the cycle boundary
///   rather than after 16 exponential levels.
///
/// `Type` is only `PartialEq` (not `Hash`/`Eq` — `Float` blocks `Eq`), so the
/// memo uses linear-scan `Vec`s; the distinct-type count per wrapper is tiny
/// (a handful), so the scan is cheaper than the hashing it replaces.
struct BakeMemo {
    done: Vec<(Type, usize)>,
    in_progress: Vec<Type>,
}

impl BakeMemo {
    fn new() -> Self {
        BakeMemo {
            done: Vec::new(),
            in_progress: Vec::new(),
        }
    }

    /// Offset of an already-fully-baked identical type, if any.
    fn lookup_done(&self, ty: &Type) -> Option<usize> {
        self.done.iter().find(|(t, _)| t == ty).map(|(_, off)| *off)
    }

    /// Is this exact type currently on the bake stack (a back-edge → cycle)?
    fn is_in_progress(&self, ty: &Type) -> bool {
        self.in_progress.iter().any(|t| t == ty)
    }
}

impl DescriptorBlob {
    fn new() -> Self {
        DescriptorBlob { buf: Vec::new() }
    }

    fn align4(&mut self) {
        while !self.buf.len().is_multiple_of(4) {
            self.buf.push(0);
        }
    }

    fn pos(&self) -> usize {
        self.buf.len()
    }

    /// Reserve a 24-byte descriptor record at a 4-aligned offset; return it.
    fn reserve_desc(&mut self) -> usize {
        self.align4();
        let at = self.buf.len();
        self.buf.extend_from_slice(&[0u8; DESC_SIZE]);
        at
    }

    fn write_i32(&mut self, at: usize, v: i32) {
        self.buf[at..at + 4].copy_from_slice(&v.to_le_bytes());
    }

    fn set_kind(&mut self, desc_at: usize, kind: DescriptorKind) {
        self.write_i32(desc_at + OFF_KIND, kind as i32);
    }

    /// Set a self-relative offset stored at `field_at` to point at `target_at`.
    fn set_self_rel(&mut self, field_at: usize, target_at: usize) {
        let rel = target_at as isize - field_at as isize;
        self.write_i32(field_at, rel as i32);
    }

    /// Append a `BlobStr` (`[len:i32 | bytes]`, NOT NUL-terminated); return its
    /// offset (the `len` field).
    fn append_str(&mut self, s: &str) -> usize {
        self.align4();
        let at = self.buf.len();
        self.buf.extend_from_slice(&(s.len() as i32).to_le_bytes());
        self.buf.extend_from_slice(s.as_bytes());
        at
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Concrete-type-arg substitution — the closure-walk substitution shared with
// the platform schema generator (BC §3, platform-interface.md §6.0).
//
// The substitution primitives (`collect_var_ids`, `subst_for_ctor_fields`) live
// once in `crate::schema` (their canonical home); this baker consumes them so
// the walk is a single routine across the two emitters (the descriptor blob here
// + the schema text there). The shared asset is the WALK, not the output form.
// ════════════════════════════════════════════════════════════════════════════

use crate::schema::subst_for_ctor_fields;

// ════════════════════════════════════════════════════════════════════════════
// Discovery — swap ALL symbol tables (S76 §5).
// ════════════════════════════════════════════════════════════════════════════

/// Compute the traced set by iterating ALL module symbol tables.
///
/// Per module: take its GOT base; select `Def { got_slot: Some(slot), .. }`
/// entries whose GOT slot holds a non-zero callable address (the single source
/// of truth, BC §3 invariant 3 — NOT `entry.code`). Skip constrained-poly base
/// names + overloaded base names (dispatch placeholders). Arity/param/result
/// types come from `entry.scheme.ty` (must be `Type::Fn`, else skip).
///
/// No project-root filter, primitives included — completeness by construction
/// (`tracing.md` §3.5). Free function so it is unit-testable against a
/// hand-built `DashMap` without a full `FnCompiler`.
fn discover_traced_fns_from_tables<C, L>(
    symbol_tables: &dashmap::DashMap<cranelisp_types::ModuleFullPath, cranelisp_types::SymbolTable<C, L>>,
) -> Vec<TracedFnInfo>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut traced = Vec::new();
    for module_guard in symbol_tables.iter() {
        let module_path = module_guard.key();
        let table = module_guard.value();
        for (name, entry) in table.all_symbols() {
            let ModuleEntry::Def { scheme, .. } = entry else {
                continue;
            };
            // The GOT slot rides on the callable `DefKind` variant (S83
            // Option-A reshape); `callable_got_slot()` answers `Some` ONLY for
            // directly-callable kinds (concrete user fns, primitives,
            // constructors, platform effects) and `None` for the constrained-poly
            // base names + overloaded base names (dispatch placeholders, not
            // directly callable — their mono specialisations / variants are
            // slotted separately and traced on their own). The former explicit
            // constrained/overloaded skip is now structural in the accessor.
            let Some(slot) = entry.callable_got_slot() else {
                continue;
            };
            // Read the callable address from the GOT slot (the single source of
            // truth). 0 = not yet populated / no real code → skip. This includes
            // primitives (code: None) whose ptrs live in the GOT.
            let code_ptr = table.got.load_slot(slot) as i64;
            if code_ptr == 0 {
                continue;
            }
            // Arity + param/result types from the scheme.
            let Type::Fn(params, ret) = &scheme.ty else {
                continue;
            };
            traced.push(TracedFnInfo {
                name: format!("{module_path}/{name}"),
                module_path: module_path.clone(),
                got_slot: slot,
                arity: params.len(),
                param_types: params.clone(),
                result_type: (**ret).clone(),
            });
        }
    }
    traced
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Build a substitution from a polymorphic ADT's constructor-field type
    /// vars to the call site's concrete `type_args`. Replicates
    /// `src/display.rs::build_adt_subst`: collect the var ids used across the
    /// type's constructor fields (in first-occurrence order) and map them
    /// positionally to `type_args`.
    fn build_adt_subst(&self, fqtn: &FQTypeName, type_args: &[Type]) -> HashMap<TypeId, Type> {
        let Some(type_def) = self.ctx.lookup_type_def(fqtn) else {
            return HashMap::new();
        };
        let metas = self.ctx.constructor_metas(&type_def);
        // Reuse the shared closure-walk substitution (canonical home
        // `crate::schema`) so the baker and the schema generator compute the
        // positional var→arg mapping identically.
        let field_type_lists: Vec<Vec<Type>> = metas
            .iter()
            .map(|meta| meta.fields.iter().map(|f| f.ty.clone()).collect())
            .collect();
        subst_for_ctor_fields(&field_type_lists, type_args)
    }

    /// Bake a single type's display descriptor into `blob`, returning the byte
    /// offset of the descriptor record (the blob root for that type).
    ///
    /// Termination is by `memo` (FIXME 0340): a type already on the bake stack
    /// (`in_progress`) is a cycle back-edge and degrades to `TypeVar`; a type
    /// already fully baked (`done`) reuses its offset (DAG sharing). The
    /// `MAX_DESCRIPTOR_DEPTH` guard remains as a defensive backstop for any
    /// non-cyclic-but-pathologically-deep nesting the type-identity memo would
    /// not catch (it cannot recur forever because compound types are recorded in
    /// `in_progress` before their fields are visited).
    fn bake_descriptor(
        &self,
        blob: &mut DescriptorBlob,
        memo: &mut BakeMemo,
        ty: &Type,
        depth: usize,
    ) -> usize {
        if depth >= MAX_DESCRIPTOR_DEPTH {
            let d = blob.reserve_desc();
            blob.set_kind(d, DescriptorKind::TypeVar);
            return d;
        }
        match ty {
            Type::Int => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Int);
                d
            }
            Type::Bool => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Bool);
                d
            }
            Type::Float => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Float);
                d
            }
            Type::String => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::String);
                d
            }
            Type::Fn(_, _) => {
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::Fn);
                d
            }
            Type::Var(_) | Type::TyConApp(_, _) => {
                // Residual type variable / higher-kinded application with no
                // concrete instantiation at this site — bare-value fallback.
                let d = blob.reserve_desc();
                blob.set_kind(d, DescriptorKind::TypeVar);
                d
            }
            Type::ADT(fqtn, type_args) => {
                // Cycle back-edge: this exact ADT is already being baked higher
                // on the stack — degrade to TypeVar (bare value) to terminate.
                if memo.is_in_progress(ty) {
                    let d = blob.reserve_desc();
                    blob.set_kind(d, DescriptorKind::TypeVar);
                    return d;
                }
                // DAG sharing: an identical ADT already fully baked — reuse it.
                if let Some(off) = memo.lookup_done(ty) {
                    return off;
                }
                memo.in_progress.push(ty.clone());
                let off = if fqtn.name.as_ref() == "Vec" {
                    self.bake_vec(blob, memo, type_args.first(), depth)
                } else {
                    self.bake_adt(blob, memo, fqtn, type_args, depth)
                };
                memo.in_progress.retain(|t| t != ty);
                memo.done.push((ty.clone(), off));
                off
            }
        }
    }

    /// Bake a `Vec` descriptor: kind=Vec with exactly one child (element).
    fn bake_vec(
        &self,
        blob: &mut DescriptorBlob,
        memo: &mut BakeMemo,
        elem: Option<&Type>,
        depth: usize,
    ) -> usize {
        let root = blob.reserve_desc();
        blob.set_kind(root, DescriptorKind::Vec);
        if let Some(elem_ty) = elem {
            let child = self.bake_descriptor(blob, memo, elem_ty, depth + 1);
            blob.set_self_rel(root + OFF_CHILD0, child);
        }
        root
    }

    /// Bake an `Adt` descriptor: kind=Adt with a type-name BlobStr + a CtorTable.
    ///
    /// CtorTable: `[n_ctors:i32 | single_match:i32 | CtorEntry[n]]`.
    /// CtorEntry: `[tag:i32 | n_fields:i32 | name_off:i32 | fields_off:i32]`.
    /// `fields_off` → array of `n_fields` self-relative i32 offsets, each → a
    /// field child descriptor (concrete-substituted).
    fn bake_adt(
        &self,
        blob: &mut DescriptorBlob,
        memo: &mut BakeMemo,
        fqtn: &FQTypeName,
        type_args: &[Type],
        depth: usize,
    ) -> usize {
        let root = blob.reserve_desc();
        blob.set_kind(root, DescriptorKind::Adt);

        let Some(type_def) = self.ctx.lookup_type_def(fqtn) else {
            // No type def available — leave Adt with no name/ctors; the walker
            // falls back to the bare value.
            return root;
        };
        let metas = self.ctx.constructor_metas(&type_def);
        // single_match: exactly one constructor whose name equals the type name
        // (spec §1.5 — suppress the `Type.` prefix, e.g. `(Point 3 4)`).
        let type_name = fqtn.name.as_ref();
        let single_match = type_def.constructors.len() == 1
            && type_def
                .constructors
                .first()
                .map(|c| c.as_ref() == type_name)
                .unwrap_or(false);

        // Concrete-type substitution for polymorphic fields.
        let subst = self.build_adt_subst(fqtn, type_args);

        // Bake child field descriptors FIRST (so their offsets exist), tracking
        // per-constructor (tag, ctor_name, Vec<field_desc_off>).
        struct CtorBake {
            tag: i32,
            name: String,
            field_descs: Vec<usize>,
        }
        let mut ctor_bakes: Vec<CtorBake> = Vec::with_capacity(metas.len());
        for (ctor_name, meta) in type_def.constructors.iter().zip(metas.iter()) {
            let mut field_descs = Vec::with_capacity(meta.fields.len());
            for field in &meta.fields {
                let concrete = cranelisp_types::apply(&subst, &field.ty);
                let fd = self.bake_descriptor(blob, memo, &concrete, depth + 1);
                field_descs.push(fd);
            }
            ctor_bakes.push(CtorBake {
                tag: meta.tag as i32,
                name: ctor_name.as_ref().to_string(),
                field_descs,
            });
        }

        // Bake the type-name BlobStr.
        let type_name_off = blob.append_str(type_name);

        // Bake ctor-name BlobStrs and per-ctor field-offset arrays.
        // ctor_name_off[i], fields_arr_off[i] (0 if no fields).
        let mut ctor_name_offs = Vec::with_capacity(ctor_bakes.len());
        let mut fields_arr_offs = Vec::with_capacity(ctor_bakes.len());
        for cb in &ctor_bakes {
            let name_off = blob.append_str(&cb.name);
            ctor_name_offs.push(name_off);
            if cb.field_descs.is_empty() {
                fields_arr_offs.push(None);
            } else {
                // An array of n self-relative i32 offsets, each pointing at the
                // already-baked field child descriptor.
                blob.align4();
                let arr_at = blob.pos();
                // Reserve the array slots.
                for _ in &cb.field_descs {
                    blob.buf.extend_from_slice(&0i32.to_le_bytes());
                }
                for (i, &fd) in cb.field_descs.iter().enumerate() {
                    blob.set_self_rel(arr_at + i * 4, fd);
                }
                fields_arr_offs.push(Some(arr_at));
            }
        }

        // Bake the CtorTable. Header [n_ctors | single_match] then entries.
        blob.align4();
        let ctab = blob.pos();
        blob.buf
            .extend_from_slice(&(ctor_bakes.len() as i32).to_le_bytes());
        blob.buf
            .extend_from_slice(&(if single_match { 1i32 } else { 0i32 }).to_le_bytes());
        let entries_at = blob.pos();
        // Reserve entry records (4 i32 = 16 bytes each).
        for _ in &ctor_bakes {
            blob.buf.extend_from_slice(&[0u8; 16]);
        }
        for (i, cb) in ctor_bakes.iter().enumerate() {
            let e = entries_at + i * 16;
            blob.write_i32(e, cb.tag); // tag
            blob.write_i32(e + 4, cb.field_descs.len() as i32); // n_fields
            blob.set_self_rel(e + 8, ctor_name_offs[i]); // name_off (self-rel)
            match fields_arr_offs[i] {
                Some(arr_at) => blob.set_self_rel(e + 12, arr_at), // fields_off
                None => blob.write_i32(e + 12, 0),
            }
        }

        // Link root.name_off + root.ctors_off (self-relative).
        blob.set_self_rel(root + OFF_NAME, type_name_off);
        blob.set_self_rel(root + OFF_CTORS, ctab);
        root
    }

    /// Bake the full descriptor set for one traced function — one blob holding
    /// the param descriptors (in order) and the result descriptor — and emit it
    /// as a read-only data symbol. Returns the per-param + result blob-root byte
    /// offsets plus the `DataId`, so the wrapper can materialise each
    /// descriptor's address via `global_value` against the symbol.
    ///
    /// Packing all of one wrapper's descriptors into ONE data symbol matches
    /// `tracing.md` §3.4 "one data symbol per wrapper's descriptor set, one
    /// relocation per wrapper reference."
    fn bake_descriptor_blob(
        &mut self,
        tf: &TracedFnInfo,
        span: Span,
    ) -> Result<DescriptorSet, CranelispError> {
        let mut blob = DescriptorBlob::new();
        // One memo for the whole wrapper's descriptor set: param + result types
        // that coincide share a single baked record (DAG), and recursive ADTs
        // terminate at the cycle back-edge (FIXME 0340 — collapses the former
        // exponential re-bake to linear in distinct types).
        let mut memo = BakeMemo::new();
        let mut param_roots = Vec::with_capacity(tf.param_types.len());
        for pty in &tf.param_types {
            param_roots.push(self.bake_descriptor(&mut blob, &mut memo, pty, 0));
        }
        let result_root = self.bake_descriptor(&mut blob, &mut memo, &tf.result_type, 0);

        // Read-only, non-thread-local anonymous data.
        let data_id = self
            .module
            .declare_anonymous_data(false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare trace descriptor data for '{}': {e}", tf.name),
                location: ErrorLocation::from_span(span),
            })?;
        let mut desc = cranelift_module::DataDescription::new();
        // 4-byte alignment matches `align_of::<DisplayDescriptor>() == 4`.
        desc.set_align(4);
        desc.define(blob.buf.into_boxed_slice());
        self.module
            .define_data(data_id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define trace descriptor data for '{}': {e}", tf.name),
                location: ErrorLocation::from_span(span),
            })?;

        Ok(DescriptorSet {
            data_id,
            param_roots,
            result_root,
        })
    }

    /// Discover the traced set by iterating ALL module symbol tables (S76 §5).
    ///
    /// Per module: take its GOT base; select `Def { got_slot: Some(slot), .. }`
    /// entries whose GOT slot holds a non-zero callable address (the single
    /// source of truth, BC §3 invariant 3 — NOT `entry.code`). Skip
    /// constrained-poly base names (dispatch placeholders). Arity/param/result
    /// types come from `entry.scheme.ty` (must be `Type::Fn`, else skip).
    ///
    /// No project-root filter, primitives included — completeness by
    /// construction (`tracing.md` §3.5).
    fn discover_traced_fns(&self) -> Vec<TracedFnInfo> {
        discover_traced_fns_from_tables(self.ctx.symbol_tables)
    }

    /// Discard a body result by decrementing its RC if it is heap-allocated.
    /// Used by both `compile_trace` and `compile_trace_no_swap` to drop the
    /// body value (the trace result is the Trace ADT, not the body's value).
    ///
    /// The dec MUST be category-driven: a `Mixed` body type (a sum ADT that
    /// can be a bare nullary tag OR a heap pointer — e.g. `(Option a)`) must
    /// use the nullary-guarded dec, else a nullary body value (e.g. `None` = 0)
    /// makes the unguarded `atomic_rmw Sub [0+8]` fault at address 0x8 (the
    /// RC offset on a null base) — the trace ADT-render crash, FIXME 0284.
    /// `AlwaysHeap` is always a real pointer so the plain dec is sound.
    fn emit_body_discard(&mut self, body_val: Value, body: &Expr) {
        let Some(ty) = body.inferred_type().cloned() else {
            return;
        };
        match crate::heap::HeapCategory::classify(&ty, Some(self.ctx.symbol_tables)) {
            crate::heap::HeapCategory::AlwaysHeap => {
                crate::heap::emit_rc_dec(
                    &mut self.builder,
                    self.module,
                    body_val,
                    self.ctx.dealloc_func_id,
                    None,
                );
            }
            crate::heap::HeapCategory::Mixed => {
                crate::heap::emit_rc_dec_guarded(
                    &mut self.builder,
                    self.module,
                    body_val,
                    self.ctx.dealloc_func_id,
                    None,
                    true,
                );
            }
            crate::heap::HeapCategory::NeverHeap => {}
        }
    }

    /// Compile a `(trace body)` expression.
    ///
    /// Returns a `Value` that is a heap pointer to a `Trace` ADT.
    pub(crate) fn compile_trace(
        &mut self,
        _modules: &[cranelisp_types::Symbol],
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Discovery is internal now (S76 §5): iterate all symbol tables.
        let traced = self.discover_traced_fns();
        if traced.is_empty() {
            // Degenerate program with no GOT-slotted callable — fall back to the
            // empty-trace path (still emits collect_trace, last).
            return self.compile_trace_no_swap(body, span);
        }

        // Group by defining module (each module has its own GOT table + GOT
        // data symbol). Grouping by `module_path` rather than the raw
        // `got_base` i64 lets each group reference its own GOT **data symbol**
        // for relocation-based addressing (FIXME 0275) — the raw `got_base` is
        // only a stale compiling-process address and is never emitted.
        let mut got_groups: Vec<(cranelisp_types::ModuleFullPath, Vec<&TracedFnInfo>)> = Vec::new();
        for tf in &traced {
            if let Some(grp) = got_groups
                .iter_mut()
                .find(|(m, _)| *m == tf.module_path)
            {
                grp.1.push(tf);
            } else {
                got_groups.push((tf.module_path.clone(), vec![tf]));
            }
        }

        // No object-mode exception: the `primitives` group swaps in ALL modes
        // like every other module (FIXME 0280, S76 Wave 3). Pre-0280 the
        // synthetic `primitives` GOT was a runtime HEAP allocation
        // (`GotTable::new()`), so `__cranelisp_got_primitives` was not a
        // link-time symbol and the group was skipped in object mode (the
        // deleted `is_pic` guard). Per FIXME 0280 the primitives GOT is now
        // constructed over an EXPORTED static slab
        // (`cranelisp_primitives::PRIMITIVES_GOT_SLAB`,
        // `#[unsafe(export_name = "__cranelisp_got_primitives")]`), so the
        // symbol resolves at `ld` time exactly like `__cranelisp_got_{user}` —
        // referencing it as `Linkage::Import` is sound in object mode too. The
        // primitives group therefore stays in `got_groups`, and extern
        // primitives now appear in `--link` trace trees (only inline primitives
        // `+`, `-`, … remain structurally invisible in all modes).

        // Declare trace runtime functions in the module (idempotent for Import linkage).
        let swap_id = self.declare_trace_extern("cranelisp_trace_swap_got", 4, true, span)?;
        let restore_id =
            self.declare_trace_extern("cranelisp_trace_restore_got", 2, false, span)?;
        let collect_id = self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;

        // For each GOT group: compile wrappers and emit swap_got call. The saved
        // value carries the GOT base (a `global_value`, recomputed for restore)
        // alongside the swap's saved-GOT pointer.
        let mut swap_results: Vec<(GotGroupRelocs, Value)> = Vec::new();

        for (module_path, group) in &got_groups {
            let n = group.len();

            // --- GOT base: relocation against the module's GOT data symbol ---
            // (NOT the stale compiling-process `got_base` iconst). Declared
            // `Linkage::Import`; emitted (object) / registered (JIT) elsewhere.
            // This is the same pattern `apply.rs::compile_direct_call` uses.
            let got_sym = crate::compiler::got_data_symbol_name(module_path);
            let got_data_id = self
                .module
                .declare_data(&got_sym, Linkage::Import, false, false)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare GOT data '{got_sym}': {e}"),
                    location: ErrorLocation::from_span(span),
                })?;

            // --- slots buffer: read-only, known at compile time. Emitted as a
            // data symbol holding the u32 slot indices (no leak, no absolute). ---
            let mut slots_bytes = Vec::with_capacity(n * 4);
            for tf in group {
                slots_bytes.extend_from_slice(&(tf.got_slot as u32).to_le_bytes());
            }
            let slots_data_id = self.emit_ro_data(&slots_bytes, 4, "trace slots", span)?;

            // --- wrappers buffer: WRITTEN at runtime (func_addr fill below),
            // READ by swap_got. Mutable data symbol (no leak, no absolute). ---
            let wrappers_data_id =
                self.emit_zero_data(n * 8, 8, true, "trace wrappers", span)?;

            // --- originals buffer: WRITTEN at runtime (the pre-swap GOT-slot
            // load below), READ by each wrapper to reach the ORIGINAL fn. This
            // captures the original code pointer from the live GOT *before* the
            // swap installs the wrappers, so the wrapper reaches the real fn and
            // not itself — late-bound, mode-agnostic, no baked absolute. ---
            let originals_data_id =
                self.emit_zero_data(n * 8, 8, true, "trace originals", span)?;

            // Materialise the GOT base once (one global_value → one relocation
            // in object mode; JIT patches it to the runtime slab base).
            let got_base_val = {
                let gv = self.module.declare_data_in_func(got_data_id, self.builder.func);
                self.builder.ins().global_value(types::I64, gv)
            };

            // Materialise the wrappers + originals buffer base addresses.
            let wrappers_base = {
                let gv = self.module.declare_data_in_func(wrappers_data_id, self.builder.func);
                self.builder.ins().global_value(types::I64, gv)
            };
            let originals_base = {
                let gv = self.module.declare_data_in_func(originals_data_id, self.builder.func);
                self.builder.ins().global_value(types::I64, gv)
            };

            // For each function:
            //   (a) capture the ORIGINAL code ptr from the live GOT slot into
            //       the originals buffer (BEFORE the swap),
            //   (b) compile its wrapper and store the wrapper's func_addr into
            //       the wrappers buffer.
            for (i, tf) in group.iter().enumerate() {
                let buf_off = (i * 8) as i32;

                // (a) original = load(got_base + slot*8); store into originals[i].
                let slot_addr = self
                    .builder
                    .ins()
                    .iadd_imm(got_base_val, (tf.got_slot * 8) as i64);
                let orig_ptr = self.builder.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    slot_addr,
                    0,
                );
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), orig_ptr, originals_base, buf_off);

                // (b) compile wrapper (reads originals[i] for the indirect call).
                let wrapper_id =
                    self.compile_trace_wrapper_fn(tf, originals_data_id, i, span)?;
                let func_ref = self
                    .module
                    .declare_func_in_func(wrapper_id, self.builder.func);
                let wrapper_ptr_val = self.builder.ins().func_addr(types::I64, func_ref);
                self.builder.ins().store(
                    MemFlags::trusted(),
                    wrapper_ptr_val,
                    wrappers_base,
                    buf_off,
                );
            }

            // Emit cranelisp_trace_swap_got(got_base, n_slots, slots_ptr, wrappers_ptr).
            let slots_val = {
                let gv = self.module.declare_data_in_func(slots_data_id, self.builder.func);
                self.builder.ins().global_value(types::I64, gv)
            };
            let n_val = self.builder.ins().iconst(types::I64, n as i64);
            let swap_ref = self.module.declare_func_in_func(swap_id, self.builder.func);
            let call = self.builder.ins().call(
                swap_ref,
                &[got_base_val, n_val, slots_val, wrappers_base],
            );
            let saved_got_val = self.builder.inst_results(call)[0];
            swap_results.push((
                GotGroupRelocs {
                    got_data_id,
                },
                saved_got_val,
            ));
        }

        // Compile the body expression.
        // Disable sparkability analysis inside trace bodies — trace must
        // execute sequentially to produce deterministic trace trees.
        let saved_trace = self.in_trace_body;
        self.in_trace_body = true;
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let body_result = self.compile_expr(body)?;
        self.in_tail_position = saved_tail;
        self.in_trace_body = saved_trace;

        // Discard body result (dec RC if it is heap-allocated).
        // The trace result is the Trace ADT, not the body's value.
        self.emit_body_discard(body_result, body);

        // Restore GOTs in reverse order (for clean nesting semantics). The GOT
        // base is recomputed via `global_value` against the same GOT data
        // symbol — never the stale compiling-process `got_base` (FIXME 0275).
        let restore_ref = self
            .module
            .declare_func_in_func(restore_id, self.builder.func);
        for (relocs, saved_got_val) in swap_results.iter().rev() {
            let gv = self
                .module
                .declare_data_in_func(relocs.got_data_id, self.builder.func);
            let got_base_val = self.builder.ins().global_value(types::I64, gv);
            self.builder
                .ins()
                .call(restore_ref, &[got_base_val, *saved_got_val]);
        }

        // Call cranelisp_collect_trace() -> Trace ADT heap ptr. Emitted exactly
        // once, LAST — this clears the nested-trace boundary flag (intrinsics
        // guard contract; backend never clears it itself).
        let collect_ref = self
            .module
            .declare_func_in_func(collect_id, self.builder.func);
        let collect_call = self.builder.ins().call(collect_ref, &[]);
        Ok(self.builder.inst_results(collect_call)[0])
    }

    /// Fallback path used when discovery finds no traced functions.
    ///
    /// Evaluates the body (discards result) and returns an empty TraceCall via
    /// `cranelisp_collect_trace`. The trace stack will be empty so it returns a
    /// minimal TraceCall with the root "::trace::" name.
    fn compile_trace_no_swap(
        &mut self,
        body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;
        let body_result = self.compile_expr(body)?;
        self.in_tail_position = saved_tail;

        // Discard body result.
        self.emit_body_discard(body_result, body);

        // Return empty trace from collect_trace (handles empty stack gracefully).
        let collect_id = self.declare_trace_extern("cranelisp_collect_trace", 0, true, span)?;
        let collect_ref = self
            .module
            .declare_func_in_func(collect_id, self.builder.func);
        let call = self.builder.ins().call(collect_ref, &[]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Declare a trace runtime extern function in the module.
    ///
    /// `n_params`: number of `i64` parameters.
    /// `has_return`: whether the function returns an `i64`.
    ///
    /// Idempotent: re-declaring with the same signature returns the existing FuncId.
    /// The named symbol resolves from `cranelisp_intrinsics::catalog::intrinsics_table()`
    /// in every mode (S76 §4.2).
    fn declare_trace_extern(
        &mut self,
        name: &str,
        n_params: usize,
        has_return: bool,
        span: Span,
    ) -> Result<FuncId, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in 0..n_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        if has_return {
            sig.returns.push(AbiParam::new(types::I64));
        }
        self.module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare trace extern '{}': {}", name, e),
                location: ErrorLocation::from_span(span),
            })
    }

    /// Compile a thin trace wrapper function for a single traced function.
    ///
    /// Wrapper signature: `(arg0: i64, ..., argN-1: i64) -> i64`
    ///
    /// Wrapper body:
    /// ```text
    /// str_ptr_0 = cranelisp_trace_format(arg0, descriptor_ptr_0)
    /// ...
    /// store str_ptrs into stack slot
    /// cranelisp_trace_enter(name_ptr, name_len, arity, array_ptr)
    /// orig_result = call_indirect(original_code_ptr, [arg0..argN-1])
    /// result_str  = cranelisp_trace_format(orig_result, result_descriptor_ptr)
    /// final       = cranelisp_trace_exit(orig_result, result_str)
    /// return final
    /// ```
    ///
    /// The original code ptr is embedded as an `iconst` -- calls bypass the GOT and
    /// call the original implementation directly. Recursive calls inside the original
    /// go through the (swapped) GOT, naturally building the call tree.
    ///
    /// Each `cranelisp_trace_format` descriptor pointer is materialised from the
    /// wrapper's baked descriptor blob via `global_value` against the blob's data
    /// symbol — mode-agnostic (JIT patches to a runtime address; object emits one
    /// relocation per reference). See `bake_descriptor_blob`.
    /// Emit a read-only data symbol with the given bytes + alignment, returning
    /// its `DataId`. Used for compile-time-constant trace buffers (slot index
    /// array, function-name bytes) — mode-agnostic, no leak, no baked absolute.
    ///
    /// `pub(crate)` so the platform-dispatch fn-name bake (`apply.rs::stamp_platform_fn_name`,
    /// S81 / FIXME 0327) reuses the same data-symbol family per BC §3.
    pub(crate) fn emit_ro_data(
        &mut self,
        bytes: &[u8],
        align: u64,
        what: &str,
        span: Span,
    ) -> Result<cranelift_module::DataId, CranelispError> {
        let data_id = self
            .module
            .declare_anonymous_data(false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare {what} data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;
        let mut desc = cranelift_module::DataDescription::new();
        desc.set_align(align);
        desc.define(bytes.to_vec().into_boxed_slice());
        self.module
            .define_data(data_id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define {what} data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;
        Ok(data_id)
    }

    /// Emit a zero-initialised data symbol of `len` bytes, returning its
    /// `DataId`. `writable = true` for runtime-filled buffers (the wrappers
    /// buffer filled by `func_addr` stores; the originals buffer filled by the
    /// pre-swap GOT-slot loads). `define` with explicit zero bytes (not
    /// `define_zeroinit`) keeps the symbol in a regular `__DATA` section so
    /// macOS `ld` does not segfault applying the wrapper's relocations against a
    /// BSS atom (same rationale as `define_module_got_data`).
    fn emit_zero_data(
        &mut self,
        len: usize,
        align: u64,
        writable: bool,
        what: &str,
        span: Span,
    ) -> Result<cranelift_module::DataId, CranelispError> {
        let data_id = self
            .module
            .declare_anonymous_data(writable, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare {what} data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;
        let mut desc = cranelift_module::DataDescription::new();
        desc.set_align(align);
        desc.define(vec![0u8; len].into_boxed_slice());
        self.module
            .define_data(data_id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define {what} data: {e}"),
                location: ErrorLocation::from_span(span),
            })?;
        Ok(data_id)
    }

    fn compile_trace_wrapper_fn(
        &mut self,
        tf: &TracedFnInfo,
        originals_data_id: cranelift_module::DataId,
        originals_index: usize,
        span: Span,
    ) -> Result<FuncId, CranelispError> {
        assert_eq!(
            tf.arity,
            tf.param_types.len(),
            "trace wrapper arity mismatch for '{}': arity={} but param_types={}",
            tf.name,
            tf.arity,
            tf.param_types.len()
        );

        // Bake the descriptor set (param + result) into one read-only data
        // symbol. Done before building the wrapper IR so the DataId exists.
        let desc_set = self.bake_descriptor_blob(tf, span)?;

        // Wrapper signature: (arg0..argN-1) -> i64.
        let mut sig = self.module.make_signature();
        for _ in 0..tf.arity {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let wrapper_func_id = self
            .module
            .declare_anonymous_function(&sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare trace wrapper for '{}': {}", tf.name, e),
                location: ErrorLocation::from_span(span),
            })?;

        // Declare trace_enter (4 params), trace_exit (2 params), and trace_format (2 params).
        let enter_id = self.declare_trace_extern("cranelisp_trace_enter", 4, false, span)?;
        let exit_id = self.declare_trace_extern("cranelisp_trace_exit", 2, true, span)?;
        let format_id = self.declare_trace_extern("cranelisp_trace_format", 2, true, span)?;

        // Emit the function-name bytes as a read-only data symbol (mode-agnostic;
        // no leaked compiling-process pointer — FIXME 0275). The wrapper
        // references it via `global_value` (one relocation in object mode; JIT
        // patches the runtime address).
        let name_len = tf.name.len() as i64;
        let name_data_id = self.emit_ro_data(tf.name.as_bytes(), 1, "trace name", span)?;

        // Build and compile the wrapper IR.
        {
            let mut wrapper_func = cranelift::codegen::ir::Function::with_name_signature(
                cranelift::codegen::ir::UserFuncName::user(0, wrapper_func_id.as_u32()),
                sig.clone(),
            );
            let mut wrapper_ctx = FunctionBuilderContext::new();
            let mut wb = FunctionBuilder::new(&mut wrapper_func, &mut wrapper_ctx);

            let entry = wb.create_block();
            wb.append_block_params_for_function_params(entry);
            wb.switch_to_block(entry);
            wb.seal_block(entry);

            let args: Vec<Value> = wb.block_params(entry).to_vec();

            // Declare externs inside the wrapper function.
            let format_ref = self.module.declare_func_in_func(format_id, wb.func);
            let enter_ref = self.module.declare_func_in_func(enter_id, wb.func);

            // Materialise the descriptor blob's base address once (one
            // global_value per wrapper → one relocation in object mode).
            let blob_gv = self
                .module
                .declare_data_in_func(desc_set.data_id, wb.func);
            let blob_base = wb.ins().global_value(types::I64, blob_gv);

            // Format each parameter using cranelisp_trace_format(val, descriptor_ptr).
            // descriptor_ptr = blob_base + param_root_offset.
            let arity = tf.arity;
            let mut param_str_ptrs: Vec<Value> = Vec::with_capacity(arity);
            for (i, &root_off) in desc_set.param_roots.iter().enumerate() {
                let arg_val = args[i];
                let desc_ptr = wb.ins().iadd_imm(blob_base, root_off as i64);
                let fmt_call = wb.ins().call(format_ref, &[arg_val, desc_ptr]);
                param_str_ptrs.push(wb.inst_results(fmt_call)[0]);
            }

            // Store formatted param string pointers in a stack slot (if arity > 0),
            // then pass the slot address to cranelisp_trace_enter.
            let (params_count_val, array_ptr_val) = if arity > 0 {
                let slot = wb.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    (arity * 8) as u32,
                    3, // 2^3 = 8 byte alignment
                ));
                for (i, &str_ptr) in param_str_ptrs.iter().enumerate() {
                    wb.ins().stack_store(str_ptr, slot, (i * 8) as i32);
                }
                let count = wb.ins().iconst(types::I64, arity as i64);
                let ptr = wb.ins().stack_addr(types::I64, slot, 0i32);
                (count, ptr)
            } else {
                // No params: pass count=0, ptr=null (runtime won't dereference).
                let count = wb.ins().iconst(types::I64, 0i64);
                let ptr = wb.ins().iconst(types::I64, 0i64);
                (count, ptr)
            };

            // cranelisp_trace_enter(name_ptr, name_len, params_count, array_ptr)
            // name_ptr is a relocation against the name data symbol, NOT a baked
            // compiling-process pointer (FIXME 0275).
            let name_gv = self.module.declare_data_in_func(name_data_id, wb.func);
            let name_ptr_val = wb.ins().global_value(types::I64, name_gv);
            let name_len_val = wb.ins().iconst(types::I64, name_len);
            wb.ins().call(
                enter_ref,
                &[name_ptr_val, name_len_val, params_count_val, array_ptr_val],
            );

            // Build call signature for the original function.
            let mut orig_sig = self.module.make_signature();
            for _ in 0..tf.arity {
                orig_sig.params.push(AbiParam::new(types::I64));
            }
            orig_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = wb.import_signature(orig_sig);

            // Call the ORIGINAL via the code ptr captured in the originals
            // buffer (FIXME 0275). `compile_trace` loaded `got_base[slot]` into
            // `originals[originals_index]` BEFORE the swap installed the
            // wrappers, so this reaches the real fn — not this wrapper — and
            // bypasses the swapped GOT. The originals base is materialised by a
            // `global_value` relocation against the originals data symbol
            // (mode-agnostic), never a baked compiling-process address.
            let originals_gv = self.module.declare_data_in_func(originals_data_id, wb.func);
            let originals_base = wb.ins().global_value(types::I64, originals_gv);
            let code_ptr_val = wb.ins().load(
                types::I64,
                MemFlags::trusted(),
                originals_base,
                (originals_index * 8) as i32,
            );
            let orig_call = wb.ins().call_indirect(sig_ref, code_ptr_val, &args);
            let orig_result = wb.inst_results(orig_call)[0];

            // Format the result using cranelisp_trace_format(orig_result, result_descriptor_ptr).
            let format_ref2 = self.module.declare_func_in_func(format_id, wb.func);
            let result_desc_ptr = wb.ins().iadd_imm(blob_base, desc_set.result_root as i64);
            let result_fmt_call = wb.ins().call(format_ref2, &[orig_result, result_desc_ptr]);
            let result_str = wb.inst_results(result_fmt_call)[0];

            // cranelisp_trace_exit(orig_result, result_str) -> final result
            let exit_ref = self.module.declare_func_in_func(exit_id, wb.func);
            let exit_call = wb.ins().call(exit_ref, &[orig_result, result_str]);
            let final_result = wb.inst_results(exit_call)[0];

            wb.ins().return_(&[final_result]);
            wb.seal_all_blocks();
            wb.finalize();

            let mut ctx = cranelift::codegen::Context::for_function(wrapper_func);
            self.module
                .define_function(wrapper_func_id, &mut ctx)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to define trace wrapper for '{}': {}", tf.name, e),
                    location: ErrorLocation::from_span(span),
                })?;
        }

        Ok(wrapper_func_id)
    }
} // impl FnCompiler — trace codegen

/// Per-GOT-group relocation handles retained across the body so the restore
/// path can recompute the GOT base via the same `global_value` relocation the
/// swap path used (FIXME 0275 — never the stale compiling-process `got_base`).
struct GotGroupRelocs {
    got_data_id: cranelift_module::DataId,
}

/// One traced function's baked descriptor set: a single read-only data symbol
/// holding the param descriptors (in order) and the result descriptor, plus the
/// blob-root byte offset of each. The wrapper materialises each descriptor's
/// address as `blob_base + offset` (one `global_value` per wrapper).
struct DescriptorSet {
    data_id: cranelift_module::DataId,
    param_roots: Vec<usize>,
    result_root: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_intrinsics::heap_string::{alloc_string, read_string_as_str};
    use cranelisp_intrinsics::trace::cranelisp_trace_format;
    use cranelisp_types::{
        DefKind, ModuleEntry, ModuleFullPath, Scheme, Symbol, SymbolTable, Type, UserFnState,
        Visibility,
    };
    use dashmap::DashMap;
    use std::collections::HashMap;

    // ── Descriptor-bake round-trip against the intrinsics walker ──────────────
    //
    // These build descriptor blobs with the SAME `DescriptorBlob` primitives the
    // production bakers (`bake_descriptor` / `bake_vec` / `bake_adt`) use, then
    // exercise the intrinsics-owned `cranelisp_trace_format` against them. A pass
    // proves the arena encoding backend emits is read correctly by the formatter
    // — the cross-crate ABI is in agreement (FIXME 0254 + 0255).

    /// Run `cranelisp_trace_format` on a baked blob root and read back the result.
    fn fmt(value: i64, blob: &DescriptorBlob, root: usize) -> String {
        let ptr = unsafe { blob.buf.as_ptr().add(root) } as i64;
        let s_heap = cranelisp_trace_format(value, ptr);
        unsafe { read_string_as_str(s_heap) }.to_string()
    }

    #[test]
    fn bake_int_descriptor_round_trips() {
        let mut b = DescriptorBlob::new();
        let d = b.reserve_desc();
        b.set_kind(d, DescriptorKind::Int);
        assert_eq!(fmt(42, &b, d), "42");
        assert_eq!(fmt(-7, &b, d), "-7");
    }

    #[test]
    fn bake_bool_float_string_descriptors_round_trip() {
        let mut b = DescriptorBlob::new();
        let bd = b.reserve_desc();
        b.set_kind(bd, DescriptorKind::Bool);
        let fd = b.reserve_desc();
        b.set_kind(fd, DescriptorKind::Float);
        let sd = b.reserve_desc();
        b.set_kind(sd, DescriptorKind::String);
        assert_eq!(fmt(1, &b, bd), "true");
        assert_eq!(fmt(0, &b, bd), "false");
        assert_eq!(fmt(1.0_f64.to_bits() as i64, &b, fd), "1.0");
        let heap = alloc_string(b"hi") as i64;
        assert_eq!(fmt(heap, &b, sd), "\"hi\"");
    }

    #[test]
    fn bake_vec_of_int_descriptor_round_trips() {
        // Mirror `bake_vec`: root(Vec) with child0_off → child(Int).
        let mut b = DescriptorBlob::new();
        let root = b.reserve_desc();
        b.set_kind(root, DescriptorKind::Vec);
        let child = b.reserve_desc();
        b.set_kind(child, DescriptorKind::Int);
        b.set_self_rel(root + OFF_CHILD0, child);

        let v = cranelisp_intrinsics::vec_runtime::vec_new(3);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 10);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 20);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 30);
        assert_eq!(fmt(v, &b, root), "[10 20 30]");
    }

    /// Build an `(Option a)` instantiated at `Int` blob by hand, mirroring the
    /// exact record/ctor-table layout `bake_adt` emits, then round-trip
    /// `(Some 42)` + `None` through the walker. Exercises the polymorphic-field
    /// concrete-substitution outcome (Int field descriptor baked from `a := Int`)
    /// and the nested data path.
    #[test]
    fn bake_polymorphic_adt_concrete_substitution_round_trips() {
        let mut b = DescriptorBlob::new();
        let root = b.reserve_desc();
        b.set_kind(root, DescriptorKind::Adt);
        // Some's single field, substituted a := Int.
        let int_field = b.reserve_desc();
        b.set_kind(int_field, DescriptorKind::Int);

        let type_name = b.append_str("Option");
        let none_name = b.append_str("None");
        let some_name = b.append_str("Some");
        // fields_off array for Some (1 self-rel i32 → int_field).
        b.align4();
        let some_fields = b.pos();
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        b.set_self_rel(some_fields, int_field);

        // CtorTable [n=2 | single_match=0 | 2 entries].
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&2i32.to_le_bytes());
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 2 * 16]);
        // None tag=0 n_fields=0.
        b.write_i32(entries_at, 0);
        b.write_i32(entries_at + 4, 0);
        b.set_self_rel(entries_at + 8, none_name);
        b.write_i32(entries_at + 12, 0);
        // Some tag=1 n_fields=1.
        b.write_i32(entries_at + 16, 1);
        b.write_i32(entries_at + 16 + 4, 1);
        b.set_self_rel(entries_at + 16 + 8, some_name);
        b.set_self_rel(entries_at + 16 + 12, some_fields);

        b.set_self_rel(root + OFF_NAME, type_name);
        b.set_self_rel(root + OFF_CTORS, ctab);

        assert_eq!(fmt(0, &b, root), "Option.None");
        let some_val = alloc_adt_for_test(1, &[42]);
        assert_eq!(fmt(some_val, &b, root), "(Option.Some 42)");
    }

    /// Nested ADT: `(Option (Vec Int))` rendering `(Some [1 2])`. Exercises a
    /// field child descriptor that is itself a Vec-of-Int (two levels of nesting
    /// through the self-relative offsets).
    #[test]
    fn bake_nested_adt_round_trips() {
        let mut b = DescriptorBlob::new();
        let root = b.reserve_desc();
        b.set_kind(root, DescriptorKind::Adt);
        // Some's field is (Vec Int): Vec root + Int child.
        let vec_field = b.reserve_desc();
        b.set_kind(vec_field, DescriptorKind::Vec);
        let int_child = b.reserve_desc();
        b.set_kind(int_child, DescriptorKind::Int);
        b.set_self_rel(vec_field + OFF_CHILD0, int_child);

        let type_name = b.append_str("Option");
        let some_name = b.append_str("Some");
        b.align4();
        let some_fields = b.pos();
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        b.set_self_rel(some_fields, vec_field);

        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&1i32.to_le_bytes()); // n_ctors
        b.buf.extend_from_slice(&0i32.to_le_bytes()); // single_match
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 16]);
        b.write_i32(entries_at, 1); // tag (Some)
        b.write_i32(entries_at + 4, 1); // n_fields
        b.set_self_rel(entries_at + 8, some_name);
        b.set_self_rel(entries_at + 12, some_fields);
        b.set_self_rel(root + OFF_NAME, type_name);
        b.set_self_rel(root + OFF_CTORS, ctab);

        let v = cranelisp_intrinsics::vec_runtime::vec_new(2);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 1);
        let v = cranelisp_intrinsics::vec_runtime::vec_push_grow(v, 2);
        let some_val = alloc_adt_for_test(1, &[v]);
        assert_eq!(fmt(some_val, &b, root), "(Option.Some [1 2])");
    }

    #[test]
    fn bake_recursion_depth_guard_terminates() {
        // A blob deeper than MAX_DESCRIPTOR_DEPTH degrades to TypeVar — verify
        // the TypeVar kind renders as a bare value (the degrade target). This is
        // the terminating behaviour for recursive/cyclic ADTs.
        let mut b = DescriptorBlob::new();
        let d = b.reserve_desc();
        b.set_kind(d, DescriptorKind::TypeVar);
        assert_eq!(fmt(123, &b, d), "123");
    }

    // Allocate a heap ADT cell `[hdr | tag | field0..]` using the runtime
    // allocator, matching the base-pointer convention the walker reads.
    fn alloc_adt_for_test(tag: i64, fields: &[i64]) -> i64 {
        let payload = (1 + fields.len()) * 8;
        let base = cranelisp_intrinsics::alloc_with_rc(payload) as i64;
        unsafe {
            *((base as *mut u8).add(16) as *mut i64) = tag;
            for (i, &f) in fields.iter().enumerate() {
                *((base as *mut u8).add(24 + i * 8) as *mut i64) = f;
            }
        }
        base
    }

    // ── Discovery-set tests (S76 §5) ──────────────────────────────────────────

    fn fn_scheme(params: Vec<Type>, ret: Type) -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(params, Box::new(ret)),
        }
    }

    /// Insert a Def with a GOT slot + a fake non-zero code pointer.
    fn insert_fn(
        table: &mut SymbolTable<(), ()>,
        name: &str,
        // The GOT slot now rides on the callable `DefKind` variant (S83
        // reshape), so the caller builds the kind from the allocated slot. For
        // slot-less kinds (constrained base / overloaded base) the closure
        // ignores the slot — the entry is then slot-less and discovery skips it
        // via `callable_got_slot()`.
        make_kind: impl FnOnce(usize) -> DefKind,
        scheme: Scheme,
        fake_ptr: usize,
    ) {
        let slot = table.allocate_got_slot();
        let entry = ModuleEntry::def(scheme, make_kind(slot))
            .visibility(Visibility::Public)
            .build();
        table.insert(Symbol::from(name), entry);
        table.got.store_slot(slot, fake_ptr as *const u8);
    }

    #[test]
    fn discovery_includes_all_modules_and_primitives() {
        let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();

        let mut user = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));
        insert_fn(
            &mut user,
            "fact",
            |slot| DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot },
            },
            fn_scheme(vec![Type::Int], Type::Int),
            0x1000,
        );
        tables.insert(ModuleFullPath::from("user"), user);

        // The synthetic `primitives` module: entries carry code: None but the
        // GOT slot holds the fn ptr. Discovery must pick it up (no project-root
        // filter, primitives included).
        let mut prims = SymbolTable::<(), ()>::new(ModuleFullPath::from("primitives"));
        insert_fn(
            &mut prims,
            "str-concat",
            |slot| DefKind::Primitive { got_slot: slot },
            fn_scheme(vec![Type::String, Type::String], Type::String),
            0x2000,
        );
        tables.insert(ModuleFullPath::from("primitives"), prims);

        let traced = discover_traced_fns_from_tables(&tables);
        let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
        assert!(names.contains(&"user/fact"), "user fn must be discovered: {names:?}");
        assert!(
            names.contains(&"primitives/str-concat"),
            "primitive must be discovered (all symbol tables, primitives included): {names:?}"
        );
        // Arity + types come from the scheme.
        let prim = traced.iter().find(|t| t.name == "primitives/str-concat").unwrap();
        assert_eq!(prim.arity, 2);
        assert_eq!(prim.param_types, vec![Type::String, Type::String]);
        assert_eq!(prim.result_type, Type::String);
        assert_eq!(prim.module_path, ModuleFullPath::from("primitives"));
        assert_eq!(prim.got_slot, prims_slot_of_str_concat(&tables));
    }

    /// Read back the GOT slot the discovery should have recorded for the
    /// primitive `str-concat` (the discovery records `got_slot`, not the raw
    /// code pointer, since the wrapper reaches the original via a runtime
    /// GOT-slot load — FIXME 0275).
    fn prims_slot_of_str_concat(
        tables: &DashMap<ModuleFullPath, SymbolTable<(), ()>>,
    ) -> usize {
        let g = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        match g.get("str-concat") {
            Some(entry) => entry
                .callable_got_slot()
                .expect("str-concat must be a got-slotted Def"),
            _ => panic!("str-concat must be a got-slotted Def"),
        }
    }

    #[test]
    fn discovery_skips_constrained_poly_base_and_overloaded() {
        let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
        let mut m = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));

        // Constrained-poly base name (dispatch placeholder) — skipped.
        insert_fn(
            &mut m,
            "add",
            |_slot| DefKind::UserFn {
                fn_state: UserFnState::Constrained(Box::new(make_constrained_fn())),
            },
            fn_scheme(vec![Type::Var(0), Type::Var(0)], Type::Var(0)),
            0x3000,
        );
        // Overloaded base name — skipped.
        insert_fn(
            &mut m,
            "show",
            |_slot| DefKind::Overloaded { variants: vec![] },
            fn_scheme(vec![Type::Int], Type::String),
            0x3100,
        );
        // A real mono fn — kept.
        insert_fn(
            &mut m,
            "double",
            |slot| DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot },
            },
            fn_scheme(vec![Type::Int], Type::Int),
            0x3200,
        );
        tables.insert(ModuleFullPath::from("user"), m);

        let traced = discover_traced_fns_from_tables(&tables);
        let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
        assert!(names.contains(&"user/double"), "mono fn kept: {names:?}");
        assert!(!names.contains(&"user/add"), "constrained-poly base skipped: {names:?}");
        assert!(!names.contains(&"user/show"), "overloaded base skipped: {names:?}");
    }

    #[test]
    fn discovery_skips_empty_got_slots_and_non_fn_schemes() {
        let tables: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
        let mut m = SymbolTable::<(), ()>::new(ModuleFullPath::from("user"));

        // Def with a got_slot but the GOT slot is 0 (unpopulated) — skipped.
        let slot = m.allocate_got_slot();
        let entry = ModuleEntry::def(
            fn_scheme(vec![Type::Int], Type::Int),
            DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot },
            },
        )
        .build();
        m.insert(Symbol::from("uncompiled"), entry);
        // (no got.store_slot — slot stays null)

        // Non-Fn scheme (e.g. a zero-arg value) with a populated slot — skipped
        // (arity/types require Type::Fn).
        insert_fn(
            &mut m,
            "konst",
            |slot| DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot },
            },
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            0x4000,
        );
        tables.insert(ModuleFullPath::from("user"), m);

        let traced = discover_traced_fns_from_tables(&tables);
        let names: Vec<&str> = traced.iter().map(|t| t.name.as_str()).collect();
        assert!(!names.contains(&"user/uncompiled"), "empty GOT slot skipped: {names:?}");
        assert!(!names.contains(&"user/konst"), "non-Fn scheme skipped: {names:?}");
    }

    // A minimal ConstrainedFn for the skip test. We only need the variant
    // discriminator (`constrained_fn: Some(_)`), so any well-formed value works.
    fn make_constrained_fn() -> cranelisp_types::ConstrainedFn {
        cranelisp_types::ConstrainedFn {
            variant: cranelisp_types::DefnVariant {
                params: vec![],
                body: cranelisp_types::Expr::IntLit {
                    value: 0,
                    span: cranelisp_types::Span::SYNTHETIC,
                    inferred_type: None,
                },
                span: cranelisp_types::Span::SYNTHETIC,
            },
            scheme: fn_scheme(vec![Type::Var(0), Type::Var(0)], Type::Var(0)),
        }
    }

    // ── Descriptor-bake memoization guard (FIXME 0340 timing fix) ─────────────
    //
    // The dominant `(trace …)` codegen cost was the EXPONENTIAL re-bake of a
    // recursive / DAG-shaped ADT descriptor: `bake_descriptor` re-walked the
    // whole type at every level up to `MAX_DESCRIPTOR_DEPTH`, so a recursive
    // type (the `IntList = Nil | (Cons Int IntList)` shape below, exactly the
    // recursion class of the `Sexp`/`SList` types every macro-clause wrapper
    // carries) produced a blob whose size grew exponentially in depth — ~1.3s
    // per wrapper × ~170 discovered fns ≈ 30s+ per trace form. The `BakeMemo`
    // (cycle-break + DAG-share) collapses it to LINEAR in distinct types.
    //
    // This is a count-based guard at the bake seam: the recursive type is baked
    // ONCE (its self-reference degrades to one `TypeVar` back-edge), so the blob
    // stays small and bounded. Pre-fix the same input produced a blob orders of
    // magnitude larger (and the bake did not terminate in reasonable time).

    /// Build a recursive ADT `IntList = Nil | (Cons :Int :IntList)` into a
    /// `<(), ()>` symbol table so `lookup_type_def` / `constructor_metas` can
    /// resolve it. Returns the tables + the `IntList` ADT `Type`.
    fn recursive_intlist_tables() -> (DashMap<ModuleFullPath, SymbolTable<(), ()>>, Type) {
        use cranelisp_types::{DefKind, FQTypeName, TypeDefInfo, TypeName};

        let module = ModuleFullPath::from("user");
        let intlist_fqtn = FQTypeName {
            module: module.clone(),
            name: TypeName::from("IntList"),
        };
        let intlist_ty = Type::ADT(intlist_fqtn.clone(), vec![]);

        let mut st = SymbolTable::<(), ()>::new(module.clone());

        // The TypeDef entry (sum type: type name distinct from both ctors).
        st.insert(
            Symbol::from("IntList"),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: intlist_fqtn.clone(),
                    type_params: vec![],
                    constructors: vec![Symbol::from("Nil"), Symbol::from("Cons")],
                },
                visibility: Visibility::Public,
                docstring: None,
            },
        );

        // Nil — nullary ctor (tag 0, no fields).
        st.insert(
            Symbol::from("Nil"),
            ModuleEntry::def(
                fn_scheme(vec![], intlist_ty.clone()),
                DefKind::Constructor {
                    got_slot: 0,
                    type_name: intlist_fqtn.clone(),
                    tag: 0,
                    field_count: 0,
                    internal: false,
                    type_def: None,
                },
            )
            .visibility(Visibility::Public)
            .build(),
        );

        // Cons — data ctor (tag 1): fields [Int, IntList] — the SECOND field is
        // the recursive self-reference that drove the exponential blow-up.
        st.insert(
            Symbol::from("Cons"),
            ModuleEntry::def(
                fn_scheme(vec![Type::Int, intlist_ty.clone()], intlist_ty.clone()),
                DefKind::Constructor {
                    got_slot: 0,
                    type_name: intlist_fqtn.clone(),
                    tag: 1,
                    field_count: 2,
                    internal: false,
                    type_def: None,
                },
            )
            .visibility(Visibility::Public)
            .build(),
        );

        let tables = DashMap::new();
        tables.insert(module, st);
        (tables, intlist_ty)
    }

    /// Drive `bake_descriptor_blob` for a `TracedFnInfo` whose param/result is
    /// the recursive `IntList` ADT through a real (throwaway) `FnCompiler` over
    /// a JIT module, returning the emitted blob's byte length and descriptor
    /// record count.
    fn bake_recursive_intlist_blob_size() -> (usize, usize) {
        use cranelift::codegen::ir::{Function, UserFuncName};
        use cranelift::prelude::*;
        use cranelift_module::Module;

        let (tables, intlist_ty) = recursive_intlist_tables();
        let module_path = ModuleFullPath::from("user");

        let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
        let intrinsic_ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).unwrap();
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let func_ids: std::collections::HashMap<Symbol, cranelift_module::FuncId> =
            std::collections::HashMap::new();
        let func_arities: std::collections::HashMap<Symbol, usize> =
            std::collections::HashMap::new();

        let ctx = crate::compiler::CompileContext {
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables: &tables,
            module_aliases: &module_aliases,
            current_module: module_path.clone(),
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc.unwrap(),
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };

        let mut sig = jit.jit_module().make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig);
        let mut fctx = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut func, &mut fctx);

        let mut compiler = crate::compiler::FnCompiler::inner(
            builder,
            jit.jit_module(),
            ctx,
            1,
            std::collections::HashMap::new(),
        );

        let tf = TracedFnInfo {
            name: "user/sum".to_string(),
            module_path,
            got_slot: 0,
            arity: 1,
            param_types: vec![intlist_ty.clone()],
            result_type: intlist_ty,
        };

        // Bake via the production path; then re-bake the same type set into a
        // standalone blob to count records (the production blob is consumed by
        // define_data, so re-run bake_descriptor for the count).
        let _set = compiler
            .bake_descriptor_blob(&tf, cranelisp_types::Span::SYNTHETIC)
            .expect("bake_descriptor_blob");

        // Re-bake into a standalone DescriptorBlob to measure size + record count.
        let mut blob = DescriptorBlob::new();
        let mut memo = BakeMemo::new();
        let p = compiler.bake_descriptor(&mut blob, &mut memo, &tf.param_types[0], 0);
        let _r = compiler.bake_descriptor(&mut blob, &mut memo, &tf.result_type, 0);
        // `done` records one entry per distinct ADT baked (Int/Bool/etc are not
        // memoized — only compound ADT/Vec types are). For IntList the distinct
        // ADT set is {IntList} ⇒ exactly one done-entry, and the param + result
        // (both IntList) SHARE it (DAG).
        assert_eq!(memo.done.len(), 1, "exactly one distinct ADT baked (IntList)");
        assert_eq!(
            p, _r,
            "param and result are the same type ⇒ DAG-shared (same blob offset)"
        );
        (blob.buf.len(), memo.done.len())
    }

    #[test]
    fn recursive_adt_descriptor_bake_is_bounded_not_exponential() {
        // The recursive IntList descriptor blob must be SMALL — the recursion
        // terminates at the self-reference back-edge (one TypeVar), not after 16
        // exponential levels. A pre-fix bake produced a blob of many KB (and ran
        // for ~1s); the memoized bake is a few hundred bytes.
        let (blob_len, distinct) = bake_recursive_intlist_blob_size();
        assert_eq!(distinct, 1, "IntList baked once (linear in distinct types)");
        assert!(
            blob_len < 1024,
            "recursive-ADT descriptor blob must stay bounded (memoized cycle-break); \
             got {blob_len} bytes — a non-memoized exponential re-bake would be far larger"
        );
    }
}
