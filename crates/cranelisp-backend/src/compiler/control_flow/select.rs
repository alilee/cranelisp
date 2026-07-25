// Race/select combinator codegen: the `IO_TAG_SELECT` node emission.
//
// Compiles the user-facing combinators `race`/`select` (name-matched at the
// backend's `BuiltinFn` apply-dispatch arm — the `bind` inline-primitive
// precedent, NOT an inferred AST marker) into the documented IO-tree structure:
// a thin single-field `IO_TAG_SELECT` node whose field-0 carries a `Vec (IO a)`
// of the N branch sub-trees. The surrounding `Bind(Select, cont)` is built by
// the ordinary bind codegen — `compile_select` returns just the thin node, the
// simplest IO-node construction of the family (no continuation, no move-out, no
// null-guard).
//
// See `design/backend/io-trampoline.md §16` (the select node + bake + the
// list-carrier RC contract) and `design/int/reactor.md §2.15` (the runtime race
// + cancellation = future-drop). `select` is the sole node primitive; `race`
// builds the same node over a 2-element branch Vec (§16.3 — required as a backend
// primitive, not stdlib sugar, because the free-standing tests import `race` from
// `primitives` and cannot depend on `stdlib/`).

use cranelift::prelude::*;
use cranelift_module::Module;

use cranelisp_types::{CranelispError, ErrorLocation, MonoExpr, Span};

use crate::heap::{self, HeapAdt};

use super::FnCompiler;

/// `IO_TAG_SELECT` — emitted as the literal `6` at the bake (the backend carries
/// no `concurrency` feature and reads no platform const at codegen, the
/// `par_bind.rs` `IO_TAG_PAR = 3` / `launch.rs` `IO_TAG_LAUNCH = 5` convention).
/// Canonical home: `cranelisp_platform::IO_TAG_SELECT`.
const IO_TAG_SELECT: i64 = 6;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Compile a `(select branches)` call — `branches` is a `Vec (IO a)`.
    ///
    /// The single argument is already a compiled branch Vec (the `[..]` literal
    /// the test surface uses, or any runtime `Vec (IO a)`). It was compiled with
    /// the consuming convention (`compile_consuming_arg_list`, the `bind`
    /// precedent) so a `Var` arg is inc'd once and a temporary transfers its rc;
    /// the Select node owns exactly the one reference handed to it.
    pub(crate) fn compile_select(
        &mut self,
        arg_vals: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // arg_vals = [ branch_vec ] — the List (IO a) carrier.
        let branches_val = arg_vals[0];
        self.compile_select_node(branches_val, span)
    }

    /// Compile a `(race a b)` call — the binary special case of `select`.
    ///
    /// `race` is `(select (vec a b))`: it builds a 2-element branch Vec from its
    /// two IO arguments (reusing `compile_vec_lit`, which compiles the element
    /// expressions and takes ownership of the temporaries) and wraps it in the
    /// **identical** `IO_TAG_SELECT` node — same tag, same trampoline arm, same
    /// RC (§16.3). No second node kind; the trampoline sees one node.
    pub(crate) fn compile_race(
        &mut self,
        args: &[MonoExpr],
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Build the 2-element branch Vec (the carrier). `compile_vec_lit` compiles
        // each branch IO expression to a fresh sub-tree (rc=1 temporary) and stores
        // it into the Vec's data buffer with ownership transfer — exactly the
        // carrier `select` consumes.
        let branches_val = self.compile_vec_lit(args, span)?;
        self.compile_select_node(branches_val, span)
    }

    /// Build the thin `IO_TAG_SELECT` node (`io-trampoline.md §16.4`):
    /// `[header(16) | tag=6 | branch_vec]` — `HeapAdt::payload_size(1)` (32 bytes
    /// total). The branch Vec (rc=1) moves into field 0 with **no `rc_inc`** — a
    /// plain ownership transfer (identical to how `compile_launch` stores its
    /// detached sub-tree and `compile_par_bind` stores its branch pointers,
    /// Decision 20/24). The node owns the Vec for the whole tree lifetime; there
    /// is **no move-out and no null-guard** (select never detaches, §16.5) — the
    /// node + its branches are reclaimed uniformly by `consume_io_tree`'s
    /// `IO_TAG_SELECT` arm (`consume_vec_with(field0, consume_io_tree)`).
    fn compile_select_node(
        &mut self,
        branches_val: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;

        // Allocate the thin node: tag + 1 field = HeapAdt::payload_size(1) = 16
        // payload (32 total with the 16-byte header).
        let payload_size = HeapAdt::payload_size(1) as i64;
        let node = heap::emit_alloc(&mut self.builder, self.module, alloc_id, payload_size);

        let tag = self.builder.ins().iconst(types::I64, IO_TAG_SELECT);
        heap::heap_store(&mut self.builder, tag, node, HeapAdt::TAG_OFFSET);
        // field 0: ownership transfer of the branch Vec (rc=1) — NO inc.
        heap::heap_store(
            &mut self.builder,
            branches_val,
            node,
            HeapAdt::field_offset(0),
        );

        Ok(node)
    }
}
