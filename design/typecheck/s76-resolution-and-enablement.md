> **HISTORICAL — sprint-scoped working doc (Sprint 76).** A completed change plan, retained for the audit trail; NOT a durable subsystem reference. The durable resolution design lives in `typecheck.md` + `crates/cranelisp-typecheck/CLAUDE.md §"Bare-name resolution & the prelude fallback"` (S108 Wave-G convergence supersedes the S76 per-site resolver framing). Verify any detail here against current source before relying on it. (Triaged S109, FIXME 0578.)

# Typecheck S76 — resolution-primitive re-pointing, macro-entanglement cleanup, ctor got-slot, platform-sig entry

> **Scope.** Phase-3 design for the four typecheck-side S76 items: (1) re-point the
> `resolve_*` family at the `cranelisp-types` resolution primitive; (2) confirm
> `check_forms` stays post-expansion (Passes 2+3) and plan the macro-entanglement
> cleanup the locked three-pass model enables; (3) 0249-a constructor GOT-slotting;
> (4) the 0231 platform-sig typecheck entry. Subordinate to `design/typecheck/typecheck.md`
> (the master); cited from there. DESIGN ONLY — no source edits.
>
> Grounded in: `design/arch/macro-availability-model.md` §0 (LOCKED decision) + §0.9
> (resolution-primitive fold-in), `design/arch/bounded-contexts.md` §2 (typecheck
> invariants 10+11) + §7 ("Resolution primitive"), `crates/cranelisp-types/src/resolve.rs`
> (the NEW primitive), FIXMEs 0245 / 0231 / 0249, and `sprints/SPRINT.md` (S76).

---

## 1. Re-point the `resolve_*` family at the types primitive

### 1.1 What consolidates (the Principle 7 + 15 move)

The S76 fold-in (`macro-availability-model.md` §0.9, BC §7 "Resolution primitive")
makes name resolution — current-module lookup + import/reexport chain-follow +
§8.6.6 module-alias substitution + visibility filtering — a **single types-owned
primitive** `cranelisp_types::resolve` / `resolve_macro_head`, returning
`Resolved<C>` / `ResolveError`. Two formerly-scattered copies collapse onto it:

- **int's `SymbolTableMacroResolver`** (`src/worker.rs`) — int's, not ours.
- **typecheck's `resolve_*` family** — ours. This doc plans its re-pointing.

The duplication being retired on the typecheck side is concrete and verified:

| Typecheck-resident logic (today) | Types primitive it duplicates |
|---|---|
| `checker.rs::resolve_terminal_entry_and_home` (`:1073`) + `chain_follow_to_home` (`:1083`) | `resolve.rs::chain_follow_committed` (delegates to the same types-owned `resolve_terminal_entry_and_home` which now lives in `cranelisp-types::module`) |
| `checker.rs::resolve_module_alias` (`:1111`) — §8.6.6 longest-prefix | `resolve.rs::substitute_module_alias` |
| `checker.rs::is_in_subtree` (`:1216`) — §8.7.3 visibility | `resolve.rs::in_subtree` + `visibility_check` |
| `checker.rs::resolve_qualified` (`:1154`) — split `mod/sym`, alias, visibility | `resolve.rs::resolve_qualified` + `split_qualified` |
| typecheck-local `ResolveError` (`result.rs:76`) | `cranelisp_types::ResolveError` (relocated; §0.9 "relocated from typecheck") |

These are the same walk, written twice. Principle 7 (single source of truth) +
Principle 15 (behaviour lives with the type it operates on) put the canonical
copy on `SymbolTables` in `cranelisp-types`. The typecheck copies retire.

### 1.2 What stays typecheck-side (the load-bearing line)

The primitive owns the **walk**; typecheck owns the **view selection** and the
**kind-specific projection**. Three things explicitly stay here:

1. **View selection.** Typecheck supplies the *staging ∪ live* first-hop `View`
   (via its `SymbolTableAccess`) for Pass-2/3 body resolution. The primitive
   consults `first_hop` only for the entry-point lookup; cross-module hops read
   committed `symbol_tables` directly (dependencies are always committed —
   Principle 17 + Decision 44). This is the `View::union(staging, live)` vs
   int's `View::single(live)` distinction. **The view choice is typecheck's;
   the walk is the primitive's.** (BC §2 invariant 10; `resolve.rs` //! "the
   primitive-vs-view split".)

2. **The `From<ResolveError> for CheckError` projection.** `CheckError` is
   typecheck-owned (single-consumer per Principle 15), so the projection *into*
   it stays in `cranelisp-typecheck` (`result.rs:128`). The primitive projects
   to the types-owned neutral `CranelispError` (`resolve.rs:193`); typecheck's
   `From<ResolveError> for CheckError` becomes a thin re-projection of that same
   message+location form. Both produce identical text — `resolve.rs` rustdoc
   §"Error-projection placement" pins this. The existing
   `From<ResolveError> for CranelispError` in `result.rs:171` is now redundant
   with the types-crate one and **deletes** (it moves down with the error type).

3. **The kind-specific result shaping.** The `resolve_*` methods each project the
   generic `Resolved<C>` to their kind-specific success/error:
   - `resolve_type` → `FQTypeName` (TypeDef terminal → `info.name`; IntrinsicType
     terminal → `FQTypeName::new(home, type_name)`).
   - `resolve_trait` → `ModuleFullPath` (TraitDecl terminal → its `home`).
   - `resolve_constructor` → `TypeName` (Constructor-kind `Def` → its parent
     `type_name`; or `TypeDef` with `constructor_scheme`).
   - `resolve_qualified` → `(Option<Scheme>, Option<ResolutionGap>)` — the
     gap-in-band shape `lookup` consumes.

   These projections are **not** the walk — they read the `Resolved.entry` /
   `Resolved.home` the primitive returns and select the typecheck-relevant
   facet. They stay as thin typecheck methods (Principle 6 — one general
   primitive + thin typed wrappers).

### 1.3 The re-pointing, method by method

Each method keeps its `pub(crate)` signature (callers inside `check_forms`'s
frame are unchanged) and its kind-specific projection; its **body** changes
from "call the local chain-walk" to "build the first-hop view, call
`cranelisp_types::resolve`, project the `Resolved`".

| Method (`checker.rs`) | Re-pointing |
|---|---|
| `resolve_type` (`:714`) | Replace `self.resolve_terminal_entry_and_home(current, name)` with `cranelisp_types::resolve(symbol_tables, module_aliases, &first_hop, current, name, span)`; match `Resolved.entry` for `TypeDef`/`IntrinsicType`; map `ResolveError` → typed `ResolveError`. |
| `concrete_type_for_impl_target` (`:747`) | Same re-point; the `type_args`-embedding stays its own concern. |
| `resolve_trait` (`:777`) | Re-point; on success require `Resolved.entry` is `TraitDecl`, return `Resolved.home`. |
| `resolve_constructor` (`:806`) | Re-point; inspect `Resolved.entry` for `DefKind::Constructor` / `TypeDef + constructor_scheme`. |
| `resolve_qualified` (`:1154`) | The general primitive already handles qualified `mod/sym` (alias + visibility + `QualifiedModuleUnknown`). Re-point: call `resolve`, map `QualifiedModuleUnknown` → the in-band `ResolutionGap::SymbolTypechecked` gap shape `lookup` expects; extract the scheme from `Resolved.entry`. |
| `lookup` (`:873`) | The qualified branch (`:888-927`) delegates to `resolve_qualified`; once that is re-pointed, `lookup` is unchanged structurally. The local-scope + current-module fallback (`:879-886`) stays — it is scope-stack lookup, not symbol-table resolution. |
| `resolve_type_expr_in_module` (`:1688`) | Builds a `resolve_terminal` closure and hands it to `resolve::resolve_type_expr` (the **TypeExpr→Type** resolver in `typecheck/src/resolve.rs`, distinct from the name primitive). Re-point the closure body to call `cranelisp_types::resolve` instead of `self.resolve_terminal_entry_and_home`. The `resolve_type_expr` function itself is unchanged (it is TypeExpr structural recursion, not name resolution). |

**`typecheck/src/resolve.rs` (the TypeExpr→Type resolver) is NOT the same thing
as the name primitive and does NOT retire.** It walks `TypeExpr` syntax
(`Named`/`FnType`/`TypeVar`/`Applied`) and resolves each leaf name via the
injected `resolve_terminal` closure. After re-pointing, that closure calls the
types primitive instead of `resolve_terminal_entry_and_home` — but the
structural TypeExpr recursion remains a typecheck concern (it allocates type
vars, validates ADT arity). Only the *leaf name resolution* delegates down.

### 1.4 The retirements (delete after re-pointing)

Once every `resolve_*` method calls the primitive, these `checker.rs` helpers
have no caller and delete (relying on git for history):
`resolve_terminal_entry_and_home`, `chain_follow_to_home`, `resolve_module_alias`,
`is_in_subtree`, `probe_module_entry_owned` *if* its only remaining callers are
the retired walk (verify: it may still back `resolve_entry_in_module`, which
some test fixtures use — keep what has live callers). The typecheck-local
`ResolveError` enum + its two `From` impls (`result.rs:76-178`) delete; consumers
import `cranelisp_types::ResolveError`.

**`/dev` confirms each deletion against `cargo check` dead-code warnings — do
not pre-emptively keep a helper "in case int needs it" (feedback
`callee_api_for_caller_only`). int calls the types primitive directly; it does
not reach into typecheck's resolution.**

### 1.5 No recognition predicate on typecheck's surface

Per the §0.9 fold-in (superseding FIXME 0245's original framing): **macro-head
recognition leaves typecheck's public surface entirely.** Typecheck does NOT
expose a `is_macro_head` / recognition predicate. The within-form descent that
finds macro heads during Pass-2/3 body checks (the genuinely-typecheck part of
recognition) calls `cranelisp_types::resolve_macro_head` directly with its
staging-aware view — exactly as int's Pass-1 loop calls the same primitive with
the committed view. There is no typecheck→int and no int→typecheck dependency
for recognition; both are types queries. FIXME 0245's "author
`design/typecheck/macro-recognition.md`" deliverable is **subsumed** by this
section — there is no typecheck-interior recognition *algorithm* to author
beyond "the descent calls the types primitive." (See §2.3 for the descent's
relationship to `check_forms`.)

### 1.6 Public-API / baseline impact

**None on typecheck's surface from the re-pointing** — the `resolve_*` methods
are `pub(crate)`; deleting helpers and the local `ResolveError` *shrinks* the
crate-internal surface but does not touch `crates/cranelisp-typecheck/public-api.txt`
(those items were never public). The one baseline-visible delta is the **removal
of the typecheck-local `ResolveError`** if it (or its `From` impls) appears in
the baseline — verify against `public-api.txt`; if present, regenerate per the
baseline-diff discipline. The types-crate baseline grows (+~40 lines for
`resolve`/`resolve_macro_head`/`Resolved`/`ResolveError`) — that is **`/arch`'s**
(types is `/arch`-owned); not a typecheck baseline change.

---

## 2. `check_forms` stays post-expansion (Passes 2+3) — confirmation + cleanup

### 2.1 Confirmation: no `MacroExpander` param on `check_forms`

`check_forms(parsed, ctx, symbol_tables, module_aliases) -> Result<(), CheckError>`
runs **Passes 2 + 3** of the locked three-pass model (`macro-availability-model.md`
§0.4, §0.5): Pass 2 registers non-macro signatures into staging; Pass 3
typechecks non-macro bodies against the unioned staging+live view; atomic commit
on whole-cluster `Ok`. **Pass 1 (expand) runs in int's `process_cluster`
*before* `check_forms`** — `check_forms` receives an *already-fully-expanded*
`Vec<ParsedEntry>` and never triggers macro execution.

**Therefore `check_forms` does NOT gain a `MacroExpander` parameter.** The
`&dyn cranelisp_types::MacroExpander` capability is int's Pass-1 concern, not a
`check_forms` argument. BC §2 invariant 11 and the cluster-atomic entry surface
both pin `check_forms`'s signature at the four-arg shape (Decision 44 third
amendment); the locked decision *confirms* this rather than changing it — macro
execution is upstream, so the typecheck entry surface is untouched by W-Macro.
This is the single most important confirmation for the int waves: **no boundary
type delta on the typecheck/int seam beyond the already-authored `MacroExpander`
+ `MacroInvokeError`** (which int holds, not `check_forms`).

defmacro-clause typecheck continues via the existing clause-compile path: int's
Pass-1 loop typechecks each `defmacro`'s synthesised clause `Defn` (via
`synthesize_macro_clause_defn` + a `check_forms` call over that clause as its own
mini-cluster, or the existing inline path) before compiling it. That is int
orchestration calling `check_forms` on clause bodies — not a new typecheck entry.

### 2.2 The macro-entanglement cleanup the locked rule enables

`src/CLAUDE.md` §"Known regressions from the Wave 3a-β collapse" records two
hazards that the locked three-pass model **removes by construction**:

> **Multi-clause macro compilation through `compile_macro_clause_inline`** — the
> legacy threading of `&mut CheckState` + `&mut ModuleCheckAccumulator` is now
> no-op (the accumulator is local to `check_forms`). Some macro-clause flows
> expect cross-form context that the new shape doesn't surface.

And §4.4 of the macro-availability model traced the **"macro clause double-typecheck"**
hazard: as-built, a macro clause was typechecked+committed-to-live *mid-Pass-2*,
before the cluster's atomic check, so the same forms could be checked twice and
the same-module-helper-with-empty-GOT-slot crash could occur.

**Both are removed by the locked decision (§0.5, §0.7):**

- A macro clause's expansion-time references are **dependency-module** functions
  (compiled by Pass-1 just-in-time dependency compilation) or **same-module
  macros** (compiled in Pass 1) — **never same-module non-macro definitions**
  (forbidden, §0.1, round-trip safety §0.3). So there is **no same-module-helper
  compile interleaved with the cluster check**. The mid-cluster commit-to-live
  hazard the §4.4 trace found has no scenario left to occur in.

- Consequently `check_forms` runs over a fully-expanded form set with **no
  macro-clause typecheck embedded inside it**. The "double-typecheck" cannot
  arise: clause bodies are typechecked in Pass 1 (int-orchestrated, against
  dependencies); the cluster's non-macro bodies are typechecked once in Pass 3.

**Cleanup this enables (planned, for `/dev` typecheck + int waves):**

1. **The dead `&mut ModuleCheckAccumulator` threading through the macro-clause
   path retires.** The accumulator is already local to `check_forms` (S66
   collapse); the no-op threading through `compile_macro_clause_inline` (int-side)
   and any typecheck-side helper that still takes it for the clause path is
   removed. Typecheck-side: confirm no `check_forms`-internal helper takes a
   macro-clause-specific accumulator parameter; if a residual one exists, it
   deletes. (Most of this is int-side — `compile_macro_clause_inline` lives in
   `src/worker.rs` — so the bulk is an int `/dev` task; typecheck's part is
   confirming its clause-check entry takes only the standard `check_forms` args.)

2. **No same-module-helper resolution path in clause typecheck.** When typecheck
   checks a `defmacro` clause body in Pass 1 (int-orchestrated), name resolution
   for the clause's callees uses the **committed dependency view** — same-module
   non-macro names are structurally absent (Pass 2/3 entities not yet staged), so
   they resolve as `ResolveError` → a **clear diagnostic** rather than silently
   succeeding against an empty GOT slot. This is the §0.8 disposition flip: the
   `helper → m → f` shape is a **rejected program**, and typecheck's job is to
   produce the diagnostic "macro expansion may not reference same-module non-macro
   definition `helper`; define it in a dependency module" rather than a type
   error or a crash. **/qa authors the failing-not-ignored repro** asserting the
   diagnostic (routed via the spec change; §0.8).

3. **`compile_macro_clause_inline`'s no-op `&mut CheckState` thread** — same
   disposition: the clause-check entry takes the standard state, not a
   cross-form-context-carrying one. Typecheck confirms its clause-check surface;
   int removes the no-op argument.

> **Boundary note.** Items 1 and 3 are mostly int-side (`compile_macro_clause_inline`
> is in `src/worker.rs`). This doc plans the **typecheck-side confirmation** (the
> clause-check entry surface takes only standard `check_forms` args; no
> macro-specific accumulator/state thread crosses into typecheck). The int-side
> deletion of the no-op threading is an int `/dev` task — flagged here for the
> sprint's cross-crate coordination, filed as a cross-reference, not actioned by
> typecheck.

### 2.3 The within-form macro descent and `check_forms`

A subtlety for the int waves: because Pass 1 fully expands *before* `check_forms`,
`check_forms` should encounter **no unexpanded macro calls**. The "within-form
descent" that calls `resolve_macro_head` (§1.5) is primarily **int's Pass-1
loop**, not a `check_forms`-internal walk. Typecheck's body inference in Pass 3
walks expressions for *inference*, and if it were to encounter a residual macro
head that would be a Pass-1 bug — but for robustness, typecheck's expression
walk MAY call `resolve_macro_head` to assert-or-diagnose ("unexpanded macro call
reached typecheck — Pass 1 incomplete"). This is a defensive diagnostic, not the
expansion path. **The expansion fixpoint is entirely int's Pass-1 concern.**

---

## 3. 0249-a — constructor GOT-slot in `register_constructors`

### 3.1 The one-line change

`register_constructors` (`crates/cranelisp-typecheck/src/adt.rs:290`) builds each
constructor's `ModuleEntry::Def { kind: DefKind::Constructor, .. }` via the
`ModuleEntry::def(scheme, kind).visibility(..).param_names(..).ast(..)` builder
(`:332-343`). It currently does **not** assign a `got_slot`. 0249-a adds it,
mirroring the user-fn slotting at `program.rs:1568` (`let slot =
st.allocate_got_slot(); … .got_slot(slot)`):

```rust
// in register_constructors, per ctor, before .build():
let slot = self.current_symbol_table_mut(state).allocate_got_slot();
let mut builder = ModuleEntry::def(
    ctor_scheme,
    DefKind::Constructor { type_name: fqtn.clone(), tag: ctor.tag,
                           field_count: ctor.fields.len(), internal: ctor.internal },
)
.visibility(visibility)
.param_names(param_names)
.ast(ast)
.got_slot(slot);   // <-- NEW (0249-a)
```

Verified facts:
- `got_slot` lives on `ModuleEntry::Def` (the builder's `.got_slot(usize)` at
  `module.rs:1216`), **NOT** on the `DefKind::Constructor` payload. Confirmed.
- `SymbolTable::allocate_got_slot(&mut self) -> usize` exists (`module.rs:574`)
  and is the exact call the user-fn path uses (`program.rs:1568`).
- `register_constructors` already holds `&mut CheckState` and writes via
  `self.current_symbol_table_mut(state)` (`:347`) — the `&mut` table needed to
  call `allocate_got_slot` is in hand. (Order: allocate the slot *before*
  building, holding the `&mut` guard once; the existing `.insert(..)` at `:347`
  uses the same guard.)

### 3.2 Why this is correct now (not premature)

BC §3 "Minimal JIT-setup boundary" assumes constructor `Def`s are got-slotted
callable — `(map Some xs)` reaches the ctor *as a value* via its `got_slot`,
GOT-indirect, exactly like any user fn. Without the slot, constructor-as-value is
structurally un-callable (the value path has no address to load). This mirrors the
Decision 0048 primitives got-slotting precedent: a callable-as-value entry needs a
GOT slot at registration time. 0249-a (typecheck producer) sequences **before**
0249-b (int `derive_codegen_batch` consumer enumerates the ctor `Def` into the
compile batch so `compile_to_module` populates the slot — D41 #2). The /arch Phase-2
review (SPRINT.md Q2) confirmed: slot must exist on the entry before int enumerates
the name, else `compile_to_module` has no slot to write. **0249-a before 0249-b is
required ordering.** (Principle 8 — not an interim mechanism; this is the real
constructor-as-value path landing now that the backend assumes it.)

### 3.3 Unit test (typecheck `/dev`, co-located in `adt.rs`)

The crate's existing ADT tests (`adt.rs:1097+`) already exercise
`register_constructors` via the test fixtures. Add a focused unit test asserting
the slot assignment:

```rust
// spec: 04-adt §4.x — constructors are GOT-slotted callable values (0249-a)
#[test]
fn constructors_get_got_slots() {
    // Register a sum type (e.g. (deftype (Option a) None (Some [:a v])))
    // via the existing fixture, then assert each Constructor-kind Def entry
    // has got_slot: Some(_), and that distinct constructors get distinct slots
    // (allocate_got_slot is monotonic per table).
}
```

Assertions:
- Each `DefKind::Constructor` entry has `got_slot == Some(_)` (not `None`).
- Distinct constructors of the same type get **distinct** slots (monotonic
  allocator; no aliasing).
- A nullary constructor (e.g. `None`) is slotted too — it is addressable as a
  value (`(let [f None] f)`), not only as a bare tag at direct construction sites.
  (This is the +Neg facet: verify the slot is present even for the nullary case,
  which a naive "only data ctors need slots" implementation would skip.)

Placement: co-located `#[cfg(test)] mod tests` in `adt.rs` (unit test, owned by
`/dev` per the triad split — not a `tests/` integration test). The e2e
`(map Some xs)` coverage is `/qa`'s, gated behind 0249-b landing (SPRINT.md
W-Enablement → W-e2e).

---

## 4. 0231 — platform-sig typecheck entry

### 4.1 What int needs

FIXME 0231 (W-Integrate, platform host-wiring): int's platform loader currently
translates a `PlatformFn.type_sig` S-expr into a synthetic AST that **bypasses
typecheck** (`parse_type_sig`). The host-wiring sprint reroutes this through the
canonical path so (a) type expressions referring to schema-declared ADTs (e.g.
`(Fn [Rectangle] Int)`) resolve through the typecheck symbol-table view, and (b)
inconsistencies between the DLL's claimed type and the schema-declared shape
surface as typecheck errors at DLL load.

Typecheck's part: expose a named entry to **resolve a standalone `TypeExpr`
against an existing symbol-table view**, returning the concrete `Type`.

### 4.2 The entry — reuse the existing TypeExpr resolver, don't build a new one

This is **not new inference machinery** — it is a thin public wrapper over the
already-existing `resolve_type_expr_in_module` (`checker.rs:1688`) /
`typecheck/src/resolve.rs::resolve_type_expr` path. A platform sig is a single
type expression, not a program form, so it needs no body inference, no
generalisation — just leaf-name resolution against the symbol-table view (which,
post-§1, goes through the types primitive).

Proposed surface (FIXME 0231's shape, adapted to the post-S76 view model):

```rust
/// Typecheck a standalone type expression against the current symbol-table
/// view — int's platform loader uses this to validate PlatformFn.type_sig
/// (FIXME 0231 / 0233). Resolves leaf names (including schema-declared ADTs)
/// through the same view + resolution primitive program forms use; a name not
/// reachable from `current_module` is a CheckError (the host surfaces it as a
/// DLL-load error). Pairs with frontend's parse_type_expr (FIXME 0230).
pub fn check_type_expr(
    expr: &TypeExpr,
    ctx: &mut SymbolTableAccess,          // the view the platform module sees
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    current_module: &ModuleFullPath,
    span: Span,
) -> Result<Type, CheckError>;
```

Design notes:
- **Signature shape follows `check_forms`, not the old `CheckContext` sketch.**
  FIXME 0231's draft predates the §0.9/Decision-44 view model; the actual entry
  takes the same `SymbolTableAccess` + `SymbolTables` + `ModuleAliases` the
  cluster entry takes, so leaf-name resolution flows through the identical
  primitive + view path (§1). This keeps **one** resolution path (Principle 7) —
  the platform sig is not a special case.
- **Body**: allocate a fresh-var map for any `:a` type vars in the sig, then call
  the TypeExpr→Type resolver with a `resolve_terminal` closure that (post-§1)
  calls `cranelisp_types::resolve` against the supplied view. Returns the
  concrete `Type` or projects `ResolveError → CheckError`.
- **No new boundary type** — `TypeExpr`, `Type`, `CheckError`, `SymbolTableAccess`,
  `SymbolTables`, `ModuleAliases` all already cross the typecheck boundary. This
  is one new `pub fn`, public-API-baseline-visible (regenerate
  `crates/cranelisp-typecheck/public-api.txt` per the baseline-diff discipline
  when `/dev` lands it).

### 4.3 Coordination + seam flag

0231 pairs with FIXME 0230 (frontend `parse_type_expr`) and FIXME 0233 (int
reroutes `parse_type_sig` through 0230+0231). It also enables FIXME 0229 step 2
(host schema-validation callback cross-references schema ADT names against the
typechecked symbol-table — same path). **Coordinated landing in the W-Integrate
platform host-wiring wave**, sequenced after the int cascade defines the host
surface (SPRINT.md).

**Seam needing /arch confirmation (minor):** `check_type_expr` is a *new public
entry* on the typecheck surface — the only S76 typecheck item that grows the
public API. BC §2's "Cluster-atomic entry surface" describes `check_forms` as
"one free function per cluster"; a standalone-type-expr validator is a second,
narrower public entry. This is consistent with the bounded context (type
resolution against a view is in-scope, §2 in-scope bullet "Type inference over
every AST variant") but it is a surface addition not currently named in BC §2 or
the crate-root rustdoc. **File FIXME `target: /arch`** to name `check_type_expr`
in the typecheck bounded-context public-surface enumeration (BC §2 "Public
surface" + the lib.rs rustdoc), so the baseline-diff at PR time has a
corresponding facade/BC mention (per the two-update baseline discipline). Low
risk — it is an additive, view-respecting entry — but the surface-naming is
`/arch`'s call, not typecheck's to assert unilaterally.

---

## 5. Unit-test placement (summary)

Per the triad split (unit tests = `/dev`, co-located in-crate; integration =
`/qa` in `tests/`):

| Item | Unit test (typecheck `/dev`, in-crate) | Integration (`/qa`, `tests/`) |
|---|---|---|
| §1 resolve_* re-point | `resolve_*` projection tests stay green (existing `checker.rs`/`adt.rs` resolution tests); the types-primitive's own walk is unit-tested in `cranelisp-types::resolve` (already present, `/arch`-owned) | covered by existing module-resolution e2e |
| §2 macro-entanglement | clause-check entry takes standard args (compile-level; no new unit test needed beyond confirming the no-op thread is gone) | §0.8 rejected-program diagnostic repro — **`/qa`**, failing-not-ignored, routed with the spec change |
| §3 0249-a ctor slot | `constructors_get_got_slots` in `adt.rs` (§3.3) | `(map Some xs)` constructor-as-value — **`/qa`**, gated behind 0249-b |
| §4 0231 platform-sig | `check_type_expr` resolves a sig against a fixture view; unknown-name → `CheckError` (+Neg) | round-trip DLL sig-mismatch — **`/qa`** (FIXME 0235), W-Integrate |

---

## 6. Open seams / FIXMEs to file

| # | Target | Item | Why |
|---|---|---|---|
| 1 | `/arch` | Name `check_type_expr` in BC §2 public-surface enumeration + the typecheck lib.rs rustdoc | §4.3 — additive public entry needs a facade/BC mention for the baseline-diff two-update discipline |
| 2 | `/qa` | Rejected-program diagnostic repro (`helper → m → f` same-module clause call → clear diagnostic, not crash) | §2.2 item 2 + §0.8 — failing-not-ignored, routed with the spec change |
| — | — | FIXME 0245 — **resolve in this doc** (§1.5): recognition left typecheck's surface entirely; no `macro-recognition.md` to author. `/design` `git rm`s 0245 once this doc lands. | §0.9 superseded its premise |

**FIXME 0245 disposition.** Its deliverable ("author
`design/typecheck/macro-recognition.md`") is **moot** under the §0.9 fold-in:
recognition is a `cranelisp-types` query (`resolve_macro_head`), not a
typecheck-interior algorithm. The within-form descent (the one typecheck part)
is §1.5 + §2.3 of this doc — it *calls* the primitive, there is no discrimination
algorithm to author. As the owning `/design (typecheck)` role, the resolution is:
this doc subsumes 0245; `git rm design/arch/fixmes/0245-*.md` with a commit
naming the subsumption (the FIXME is `target: /design` — typecheck-design is the
owner, so this role resolves + deletes it).

---

## 7. Principles cited

- **Principle 7 (single source of truth)** — the chain-walk consolidates onto the
  types primitive; the two typecheck copies retire (§1.1, §1.4).
- **Principle 15 (behaviour lives with the type)** — resolution is a query over
  `SymbolTables`, so it lives in `cranelisp-types`; `CheckError` is
  typecheck-owned so its projection stays here (§1.2). *(Cited from BC/§0.9;
  Principle 15 is in the principles register though not in the triad's
  auto-imported 1–13 set — flagged for `/arch` if the import block needs it.)*
- **Principle 6 (complexity has a budget)** — one general primitive + thin typed
  wrappers; `check_type_expr` reuses the existing TypeExpr resolver rather than
  new machinery (§1.2, §4.2).
- **Principle 8 (no interim implementations)** — 0249-a lands the real
  constructor-as-value path now the backend assumes it; not a stopgap (§3.2).
- **Principle 17 (module-locality)** — the primitive's walk is module-local
  (shapes 1+2); recognition's "probe every module" predecessor retires as a net
  improvement (§1.5, BC §2 invariant 11). *(Principle 17 is in the register,
  cited via BC.)*
