---
number: 0935
target: /design
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/concreteness-types-first.md §2 (the R-24 resolution —
  static trace + differential experiment);
  crates/cranelisp-typecheck/src/program/mono_collect.rs:481,:592 (the
  collectors push `resolved.fq.symbol` — the WRITTEN spelling);
  crates/cranelisp-typecheck/src/traits/monomorphise.rs:1155-1202
  (`get_constrained_fn` raw `probe_module_entry_owned` — accepts only a
  terminal `ModuleEntry::Def`, so the bare-alias `Import` yields `None` and
  `monomorphise_call` returns `Ok(None)` SILENTLY);
  crates/cranelisp-types/src/resolve.rs:552-571 (`fq` = written spelling;
  `storage_key` = the terminal table key — the 0620 two-identity contract);
  design/arch/backend-keyed-consumer.md §1.1.2 (the alias class this repeats)
status: open
---

# Pass-4 mono collectors record the written-spelling identity, so bare member-alias and renamed-import calls silently never mint

**Target: `/design`(typecheck) — fold into the FIXME 0931 S120 collection
design; the minimal fix is also legal inside S119 W4 if `/sprint` wants the
accessor discovery live sooner. Directly relevant to W4's MEASURE-1b (the
answer is pre-empted: the F1 half is NOT a successor-discovery widening
only).**

## The defect (register row R-24, resolved)

For `(deftype (Bx a) [:a v])` + `(v (Bx 5))`, every collector condition in
`collect_local_parametric_calls` passes — including the two the requirements
register suspected (`callee_has_keyed_carrier`: the recorder writes
`VarRef::Global(storage_fq)` for the alias, `checker.rs:1733-1737`;
`resolve_terminal_fq_scoped`: the scope resolve chain-follows the alias to the
accessor `Def`). The site IS collected — but with `resolved.fq.symbol`
(`mono_collect.rs:592`), the **written spelling** `v`. `get_constrained_fn`'s
local arm (`monomorphise.rs:1171`) then raw-probes the current module for key
`v`, lands on the bare-alias `ModuleEntry::Import`, matches only
`ModuleEntry::Def` → `None` → `Ok(None)` → the drive loop's
`if let Some(mono)` skips with no diagnostic. The call then dispatches through
the polymorphic template's slot — silently, because the template HAS a slot
today (the total-concreteness reshape makes exactly this failure loud).

Differential proof at HEAD (`CRANELISP_CODEGEN_DUMP='*'`): bare `(v (Bx 5))`
compiles only `Bx`/`Bx.v`/`__expr` — no instance; dotted `(Bx.v (Bx 5))`
(written spelling == storage key) mints `user/Bx.v$user/Bx$Int`. Control
`(iden 5)` mints `user/iden$Int`.

The renamed-import shape declines identically in
`collect_imported_constrained_calls` (`:481` pushes the alias name; the
`Some(h)` arm probes the HOME module, where only the original key exists).

This is the 0620 alias class — "composing a storage identity from a written
spelling" — one line below the comment stating the rule ("The name is a
trigger, not the identity", `mono_collect.rs:574-576`).

## Second finding, binding on the fix shape

The dotted spelling's minted instance is **UNSOUND**: its CLIF carries the
`<1024`-guarded `atomic_rmw` on the loaded field word, and
`(Bx.v (Bx 1024))` crashes the REPL. The generic mono path's recheck over the
`Span::SYNTHETIC` accessor body fails to concretise the field's category, so
"fix the identity handoff" alone would convert a silent no-mint into a minted
wrong body for accessors. **The identity fix and A-MINT
(`non-concrete-producer-obligations.md` §2.3) must land together for the F1
family**; for ordinary generic fns behind renamed imports the identity fix
alone is complete.

## Fix shape

1. Collectors record `resolved.storage_key` (or read the already-recorded
   carrier's `VarRef::Global` value) — never `fq.symbol` — per the 0620
   carrier value-source rule. Verify `build_mangled_name` over the dotted
   storage key matches the name the dotted-call path already mints
   (`user/Bx.v$user/Bx$Int` — it does, by the experiment).
2. Accessor (F1) demand routes to A-MINT, not `monomorphise_call` (the second
   finding).
3. `monomorphise_call`'s `Ok(None)` early-return remains the "not a mono
   target" signal — but under the S120 reshape (slot-less templates) a demand
   that finds no instance is a loud missing-slot failure downstream, which is
   the structural cure for the silence (R-22).

Unit rows: bare-alias accessor call mints (post-A-MINT); renamed-import
generic call mints; both spellings of one call dedup to ONE instance
(`build_mangled_name` grain).

Delete this file when the S120 collection design (0931) absorbs it, or when a
S119 W4 change-set lands the fix with its rows.
