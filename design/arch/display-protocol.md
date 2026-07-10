# Display protocol — type-directed value render (List/Seq surface forms)

**Status: DESIGN (S106 Phase 3), mechanism-only, pre-implementation.** This doc answers FIXME
`design/arch/fixmes/0050-promote-list-seq-pretty-printer-aspirational.md` at the *mechanism* level.
The `repl/spec.md` §1.5 List/Seq MUST-promotion is a **follow-on sprint** (exit gate in §9); S106
does NOT promote the spec and this design does NOT block any S106 fix wave (WS-I, design-first,
time-boxed — S106 Phase-2 ruling 4).

**Containment mandate (S106 Phase-2 ruling 4).** A type-directed pretty-printer naively touches
typecheck + backend + int + stdlib — too wide to *build* in a burn-down. The design is therefore
framed as a **minimal extension of the already-landed `DisplayDescriptor` infrastructure**
(`crates/cranelisp-intrinsics/src/trace_format.rs`; `design/arch/tracing.md` §3.4), NOT a parallel
protocol. A greenfield printer that ignored `DisplayDescriptor` would be a Principle-7 duplication
defect. Everything below reuses the arena-blob descriptor vocabulary and adds exactly one kind.

---

## 1. The problem

`repl/spec.md` §1.5 renders stdlib `List` and `Seq` through the **generic ADT recursive formatter**:

```
(List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))     ; today (normative)
(Seq.SeqCons h <closure>)                               ; today (normative)
```

The aspirational target is the **surface collection form**:

```
(list 1 2 3)          ; List
(seq h +more)         ; Seq — the +more denotes an unforced lazy tail
```

The render is **type-directed**: the value's nominal type (`List` / `Seq`) selects a fold that
collapses the `Cons`/`Nil` spine into the flat surface form, rather than printing each spine
constructor. Nothing structural distinguishes a `List` from any other two-constructor recursive
ADT — the selection is **nominal**, keyed on the type's identity, not its shape.

## 2. Actors and the two render paths (before the mechanism)

Value rendering happens on **two independent paths**, and any List/Seq design must serve both or it
splits the language's display behaviour in two:

| Path | Code home | Owner | Has live symbol tables? | Consumes |
|---|---|---|---|---|
| **REPL result echo** — top-level `:Type value` display | `src/display.rs::format_value` / `format_result_value` | `/int` | **Yes** (session `symbol_tables`) | walks `TypeDefInfo` live |
| **Trace capture** — `(trace …)` value render | `cranelisp-intrinsics` `cranelisp_trace_format` | backend-emitted / intrinsics | **No** (pure walk, `--link`-safe) | a backend-baked `DisplayDescriptor` blob |

The §1.5 forms are primarily the **REPL-echo** path's concern (that is what 0050's `target: /int`
records). But the **trace** path renders the same values, and if only one path learned the `(list …)`
form the two would diverge — a `List` would print `(list 1 2 3)` at the prompt and
`(List.Cons 1 …)` inside a trace of the same session. **Consistency across the two paths is a design
invariant** (§7), and it is the reason the mechanism must live in the *shared* descriptor vocabulary,
not in a REPL-only name table.

**Not a third path.** `--run`/`--link` program *output* comes from in-language `(print …)` calls
routed through stdlib/user code — never through the compiler's ADT-display path. So there are exactly
two compiler-owned render paths; the design serves both.

## 3. Dispatch model (deliverable a) — nominal, compiler-internal, single-sourced

**Dispatch is by nominal type identity → printer selection**, resolved once where the type is known:

- **REPL-echo path:** `format_value` already has the value's static `Type` and the live
  `symbol_tables`. It reads the type's **render marker** (see §4) off the `TypeDefInfo` and, when
  present, applies the collection fold instead of the generic-ADT arm.
- **Trace path:** backend, at descriptor-bake time (it already traverses `TypeDefInfo` to build the
  `Adt` descriptor — `tracing.md` §3.4), reads the **same** marker and bakes a `Collection`
  descriptor kind (§5) instead of an `Adt` kind.

Both consumers read **one source of truth**: a render marker attached to the type definition
(`TypeDefInfo`). This is Principle 7 (single source of truth) — the marker is set once; two
formatters honour it.

**How the marker gets set — compiler-internal recognition of the built-ins (user-ratified
2026-07-10).** The originating FIXME framed two options: (a) a type-local opt-in the type author
writes, and (b) "compiler-seeded recognition of named types from a known stdlib path." The S106
design recommended (a) as a *language-visible* declarative annotation and rejected (b) on Principle
19 (no module privileged by name). **The user overruled that recommendation (2026-07-10):** the
language does **not** grow a render-annotation surface. Instead, the compiler recognizes the specific
built-in stdlib collection types (`List`, `Seq`) **internally** and stamps their render marker; a
user with special inspection requirements uses a **future Display-style trait** (§4, §9 note), not a
structural annotation. This is option (b) **narrowed and ratified**: recognition is confined to the
built-in collections, single-sourced in one compiler-side seed, and does not generalize to user
types. See §4 for the mechanism and the Principle-19 disposition.

## 4. Where the printer lives (deliverable b) — an internal render marker on the built-in collections

The printer **lives in the two existing formatters** (`format_value` + `cranelisp_trace_format`);
the type def supplies only the *data* that steers them. Two things the user settled 2026-07-10:

- **The render marker is declarative structural DATA, not code.** The type def carries "I am a
  spine-shaped collection — surface keyword `list`; spine constructor tag = C with head at field
  index H and tail at field index T; nil constructor tag = N; lazy tail?". The formatter — not user
  code — performs the fold. No method is resolved, no user code runs at render time. This is exactly
  what List/Seq need, and it keeps typecheck a passthrough (§8) and never calls user code from a
  formatter (load-bearing for the pure trace-path walk).

- **The marker is populated compiler-internally for the built-ins; there is NO language surface to
  write it** (overriding the S106 draft's language-visible-annotation recommendation — §3, §10 flag
  1). A user with special inspection requirements does **not** write a render annotation; that path
  is a **future Display-style trait** (the code-bearing custom-printer trait below), the sanctioned
  user-extensibility route. Until that trait exists, only the built-in collections render in surface
  form; a user's own two-ctor recursive ADT renders through the generic-ADT arm.

**Carrier + seed.** The marker is carried on `TypeDefInfo` (the resolved-stage type-def record both
consumers already read). Its concrete shape (the `cranelisp-types` field) lands with the
**implementation** sprint — no `cranelisp-types` edit in S106 (S106 Phase-2 "Cross-crate interface
impact — NONE"). Design-level shape:

```
// on TypeDefInfo (implementation-sprint carrier; NOT added in S106):
render: Option<CollectionRender>
struct CollectionRender {
    keyword:      Symbol,   // "list" | "seq" (surface keyword)
    spine_tag:    i32,      // constructor tag of the cons/step ctor
    nil_tag:      i32,      // constructor tag of the empty ctor
    head_field:   u32,      // field index of the element within the spine ctor
    tail_field:   u32,      // field index of the recursive tail within the spine ctor
    lazy_tail:    bool,     // true ⇒ tail is a thunk (Seq); never forced at render (§7)
}
```

The field is the **same** in both source-forks; what the user's ruling fixes is the **source** of the
data. For the built-in `List`/`Seq` it is populated by a **compiler-internal seed** — a small table
in the stdlib/primitives bootstrap that pairs the built-in collection type identities with their
`CollectionRender` data, stamped onto `TypeDefInfo` when those types are registered (the same shape as
the existing `register_option_type` seed — `Option` is already compiler-seeded there). No `deftype`
syntax carries it; no user type can set it.

**Principle-19 disposition (user-ratified narrowing, 2026-07-10).** This IS compiler-internal
recognition of specific stdlib collection types by identity — the seed names `List`/`Seq`. That is a
tension with Principle 19 (no module privileged by name), and it is exactly what the S106 draft's §3
had rejected. The user has **ACCEPTED it as a deliberate, bounded narrowing of the Principle-19
stance for the built-in collections only**: the compiler may special-case the built-in stdlib
collections' render — they are the language's own furniture — while *general* user extensibility is
routed to the future Display trait rather than a structural annotation that would re-open
name-privileging for arbitrary types. The narrowing is confined (one seed, the built-ins),
single-sourced, and does not leak into a general mechanism.

**The code-bearing custom-printer trait (future, sanctioned path).** A `Display`-like trait whose
method a type implements with arbitrary render *code* is the general user-extensibility path — and,
per the user's 2026-07-10 ruling, the **only** sanctioned one (there is no structural-annotation
surface). It is the widest possible surface — typecheck must resolve the trait + method, backend must
bake or call the method, and the formatter must *invoke user code* mid-render (in the trace path that
means calling a language closure from the pure descriptor walk — a capability it deliberately does not
have). It therefore remains **future work, out of scope for this mechanism** (§9 note). This mechanism
serves the built-in List/Seq fully without it.

## 5. Relationship to `DisplayDescriptor` (deliverable c) — EXTEND, not wrap

The design **extends** the landed descriptor ABI (`crates/cranelisp-intrinsics/src/trace_format.rs`);
it does not wrap it in a new protocol and does not fork a parallel descriptor type.

**Reused verbatim (no change):**

- The whole **arena-blob encoding**: contiguous `#[repr(C)]` records, position-independent
  **self-relative `i32` offsets**, `BlobStr` length-prefixed strings, `0 = absent`. JIT (leaked
  `Box<[u8]>`) + object-mode (`.rodata` data symbol, one relocation) baking — unchanged.
- The `DisplayDescriptor` 24-byte record shape and its `follow_self_rel` blob-walk primitives.
- `cranelisp_trace_format(value, descriptor) -> CLString` — **signature and arity `(2, true)`
  unchanged**; backend's `declare_trace_extern` is untouched. Only a new arm is added inside the walk.
- The existing `Adt` / `Vec` / scalar kinds — a `List` that has **not** opted in still renders through
  the generic `Adt` arm exactly as today (strictly additive; zero regression).

**Added (the entire mechanism surface):**

1. **One new `DescriptorKind::Collection = 8`** in the intrinsics ABI enum. (ABI note: `DescriptorKind`
   discriminants are the backend↔intrinsics contract; appending `= 8` is additive — no renumber.)
2. **A `CollectionSpec` sub-block in the blob**, referenced from a spare descriptor-record offset
   field (the record already carries `_pad`/`_pad2` reserved words and `child0_off`; the element
   descriptor reuses `child0_off`, and `CollectionSpec` hangs off a reserved offset). Its content
   mirrors §4's `CollectionRender` as self-relative blob data:
   `[ keyword: BlobStr | spine_tag: i32 | nil_tag: i32 | head_field: i32 | tail_field: i32 | lazy_tail: i32 | elem_child_off: i32 ]`.
   The `elem_child_off` points to the **element** descriptor (recursively baked — a `(list (Option Int))`
   nests `Collection(list) → elem Adt(Option) → field Int`, exactly as `Vec` nests today).
3. **One new arm in `cranelisp_trace_format`'s walk** (the `Collection` case): starting from the
   value's spine pointer, loop — read the constructor tag; while it equals `spine_tag`, render the
   `head_field` element via the element child descriptor and advance to the `tail_field` value; stop
   at `nil_tag` (or at a non-materialized lazy tail, §7). Emit `(<keyword> e1 e2 …)` (append `+more`
   when the spine stops on an unforced tail).
4. **The symmetric arm in `src/display.rs::format_value`** (int, REPL-echo): the identical fold, but
   walking the **live heap value + live `TypeDefInfo`** rather than the baked blob — same surface
   output, same `+more` rule, so the two paths are byte-identical (§7).

**Extend vs wrap — the ruling.** *Extend.* The descriptor is already a self-contained, cache-surviving,
recursive render vocabulary; collections are one more renderable shape in that vocabulary, the same
way `Vec` is. Wrapping (a `Collection` descriptor that *contains* an `Adt` descriptor and post-folds
its output) would double-encode the constructor table and re-walk the value twice — a Principle-6
complexity cost for no benefit. One kind, one fold.

## 6. What the two formatters share vs. specialize

The **fold logic is identical**; only the *substrate* differs (baked blob vs live tables). To avoid a
Principle-7 duplication between `cranelisp_trace_format` (intrinsics) and `format_value` (int), the
spine-fold is specified once here (§5 arm 3) and each formatter implements it against its own
substrate. This mirrors the existing relationship between `format_value` and `format_result_value`
(`tracing.md` §3.4 already notes the two formatters "share the heap-walking logic conceptually"). No
shared crate is warranted for ~30 lines of fold; the shared artefact is this spec section + the
consistency e2e (§9 gate 3), which pins the two implementations to the same output.

## 7. Seq laziness — the render MUST NOT force (architecture ruling)

`Seq`'s tail is a **thunk** (a closure). Forcing it means *evaluating* — which the pure
descriptor-driven `cranelisp_trace_format` structurally cannot do (no eval, no GOT dispatch, `--link`
-safe by construction). Therefore:

- **The mechanism does not force.** Both formatters render the **already-materialized** spine and emit
  **`+more`** whenever the walk reaches a spine cell whose tail is an unforced thunk (`lazy_tail` +
  a non-`nil` tail that is a closure value). A finite fully-forced `Seq` renders `(seq 1 2 3)`; an
  infinite or partially-forced `Seq` renders `(seq 1 2 +more)` and **terminates** — preserving the
  existing §1.5 MUST ("REPL MUST NOT force-evaluate the lazy tail; infinite sequence must not hang").
- **This keeps the two paths identical.** If the REPL-echo path *forced* up to a bound while trace
  could not, the paths would diverge and the consistency invariant (§2) would break. Non-forcing is
  the only design that keeps them the same — so the architecture recommends non-forcing for both.
- **"Force up to a small bound" was the alternative — the user REJECTED it (2026-07-10).** The §1.5
  aspirational text floated a forcing render; it would have been an **int-only** capability (calling
  the tail closure at display time) and would have split the two paths (trace cannot force). The user
  settled the fork (§10, flag 2) on **non-forcing**, byte-identical to the trace path — the current
  termination MUST stands; display never forces. No int-only forcing capability is built.

## 8. Cross-skill surface (deliverable d)

| Skill | Involvement | Why |
|---|---|---|
| `/arch` | the `DescriptorKind::Collection` ABI + `CollectionSpec` blob layout + the `TypeDefInfo.render` carrier shape (a `cranelisp-types` edit at the **implementation** sprint, not S106) | cross-crate descriptor ABI + boundary carrier |
| `/spec` | the §1.5 promotion wording only (**no** language-surface work — the render marker is compiler-internal, §3/§4, user 2026-07-10) | normative render form |
| `/stdlib` | own the `List`/`Seq` `deftype` *sites* whose identities the compiler-internal render seed keys on (no language-visible opt-in written on the `deftype`; the seed is compiler-side — §4) | the two recognized-collection *sites* |
| `/int` | the `format_value` collection arm (REPL-echo render) + read the render marker off live `TypeDefInfo` | the §1.5 consumer / result-echo path |
| `/backend` | the descriptor-baker `Collection` arm (bake `CollectionSpec` into the blob) | dispatch bakes a descriptor for the trace path |
| `/typecheck` | **passthrough only** — carry `TypeDefInfo.render` (populated by the compiler-internal seed) into the symbol table; **no trait resolution, no dispatch** | the declarative-data choice (§4) deliberately keeps typecheck out of the render decision |
| `/qa` | e2e: §1.5 promoted forms + the REPL-echo↔trace **consistency** guard + Seq-`+more` termination | the durable record of the promotion |

**`/typecheck` involvement is the litmus of the containment.** Under the **declarative-data** design,
typecheck only forwards a field — the "only if compile-time dispatch" condition in the Phase-2 ruling
is **not** triggered because there is no compile-time *dispatch*, only a compile-time *passthrough*.
Had we chosen the code-bearing trait (§4 — now the sanctioned *future* user-extensibility path, still
out of scope here), typecheck would resolve the trait and the surface would balloon — that is
precisely why the trait route is not part of this mechanism.

## 9. Exit gate for the promotion follow-on sprint (deliverable e)

The follow-on sprint promotes `repl/spec.md` §1.5 List/Seq to MUST and deletes FIXME 0050. Its exit
gate — all of:

1. `DescriptorKind::Collection` + `CollectionSpec` landed in the intrinsics ABI (`trace_format.rs`),
   with the backend baker arm and the `cranelisp_trace_format` walk arm; `cranelisp-types` carrier
   (`TypeDefInfo.render`) landed with its `CACHE_SCHEMA_VERSION` bump + baseline/facade cascade.
2. The **compiler-internal render marker** present on stdlib `List`/`Seq` (populated by the bootstrap
   seed — §4; **no** `/spec` language-surface work, per the user's 2026-07-10 ruling, §10 flag 1).
3. **Consistency guard GREEN:** the same `List`/`Seq` value renders **byte-identically** in the REPL
   result echo and inside a `(trace …)` of the same session (`(list 1 2 3)` / `(seq 1 2 +more)` both
   places). This is the load-bearing acceptance — it proves the mechanism lives in the shared
   vocabulary, not a REPL-only fork.
4. **Seq termination preserved:** an infinite `Seq` renders `(seq … +more)` without hanging (the
   existing §1.5 MUST is not weakened; §7 non-forcing).
5. Empty/degenerate cases: empty `List` → `(list)`, empty `Seq` → `(seq)` (or the /repl-specified
   empty form); a non-opted-in two-ctor ADT still renders generic-ADT (no accidental capture).
6. `repl/spec.md` §1.5 aspirational note removed, the `List`/`Seq` table rows re-stated as MUST with
   the surface form + `[Tested …]` annotations; FIXME 0050 deleted by `/int` (its `target`).

**Note — the code-bearing custom-printer trait is a DIFFERENT, later question.** If Cranelisp ever
wants *arbitrary* per-type render code (not just structural collection folds), that is a general
display-trait design (typecheck resolution + calling user code from a formatter — the balloon §4
excludes). It is **not** gated by this exit and should not be pulled forward; the declarative
collection render fully serves List/Seq without it.

## 10. Decisions routed to the USER — BOTH RESOLVED (user, 2026-07-10)

Two choices here were **language-/experience-visible** and the architecture routed them to the user
rather than arbitrating. The user has now settled both. They are no longer open.

1. **Does the language grow a `deftype` render-annotation surface? — RESOLVED: NO (user,
   2026-07-10).** The architecture had recommended a declarative, type-local *language-visible*
   annotation. **The user overruled that recommendation:** the language does **not** grow a
   render-annotation surface. The List/Seq collection render is handled **compiler-internally** — a
   compiler-side seed that recognizes the built-in stdlib collection types and stamps their render
   marker (§3, §4). A user with special inspection requirements implements **something like a Display
   trait** — the code-bearing custom-printer trait deferred in §4/§9 — which is now the **sanctioned
   user-extensibility path** (still future work, not this mechanism). §3/§4 reconciled to this
   ruling; the Principle-19 disposition (§4) records it as a deliberate, user-ratified narrowing of
   the no-module-privileged-by-name stance **for the built-in collections only**.

2. **Does REPL value-display force a lazy `Seq` tail up to a bound? — RESOLVED: NO (user,
   2026-07-10).** Confirmed as the architecture recommended: **non-forcing `+more`, byte-identical to
   the trace path.** Display does not diverge from trace; the current termination MUST stands; no
   int-only forcing capability is built (§7).

Both were the last design-open items; with them settled the follow-on is an ordinary implementation
sprint (§11).

## 11. Convergence status

**Mechanism design CONVERGED and both user forks SETTLED (2026-07-10).** The dispatch model (nominal,
single-sourced), the printer's home (compiler-internal render marker on the built-in collections; fold
in the two existing formatters), the `DisplayDescriptor` relationship (extend with one `Collection`
kind + `CollectionSpec` block, exact reused/added fields enumerated in §5), the cross-skill surface
(§8), and the follow-on exit gate (§9) are all specified and self-contained. No `cranelisp-types` edit
is made or owed in S106.

**Both §10 forks are now settled by the user (2026-07-10):** (1) **no language-visible
render-annotation surface** — List/Seq render is compiler-internal (built-ins seeded), general user
custom-render routes to a future Display-style trait; (2) **non-forcing Seq render** (`+more`,
byte-identical to trace). Nothing further is design-open. The follow-on is an **ordinary
implementation sprint** against this spec — no user gate, no `/spec` language-surface work
outstanding.

## Cross-references

- `crates/cranelisp-intrinsics/src/trace_format.rs` — the landed `DisplayDescriptor` ABI this design extends.
- `design/arch/tracing.md` §3.4 — the descriptor bake/emit contract (JIT + object mode).
- `repl/spec.md` §1.5 — the aspirational List/Seq forms + the current normative generic-ADT form.
- `design/arch/fixmes/0050-promote-list-seq-pretty-printer-aspirational.md` — the originating FIXME (`target: /int`; deleted at the follow-on exit gate, §9.6).
- `design/arch/bounded-contexts.md` §3 (backend bakes) / §4b invariant 12 (intrinsics hosts the formatter) / §6 (int result-display) — the surfaces the two render paths sit in.
- Principle 7 (single source of truth), Principle 19 (no module privileged by name), Principle 6 (complexity budget), Principle 8 (no interim implementations) — the axioms the containment rests on.
