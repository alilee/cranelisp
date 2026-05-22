# cranelisp-primitives — Sprint 69 facade audit (per-item analysis, grounded re-author)

**Audit triple**: `crates/cranelisp-primitives/src/lib.rs` (declared surface, 416 LOC) × `design/arch/facades/primitives.md` (binding contract, 362 LOC) × `crates/cranelisp-primitives/public-api.txt` (live boundary, 9 lines). Plus `crates/cranelisp-primitives/Cargo.toml` (dep invariants).

**Date**: 2026-05-19 (S69 Phase 3 Wave 1 — second re-author, grounded against architectural configuration).
**Auditor**: `/design` (cranelisp-primitives narrow deployment).
**Inputs frozen at**: current commit on `main` (post-S68 close `9516dfc`; Sprint 69 in progress).

**Discipline.** Per `~/.claude/projects/.../memory/feedback_audit_per_item_analysis.md` (updated 2026-05-19): every finding has a **five-block** structure (facade-expects / source-does / **design-intent grounded** / difference-implies / disposition). The earlier two versions of this audit (Sprint 68 close + first Sprint 69 re-author) dispositioned without reading the full architectural configuration that grounds the facade. **The intent grounds the disposition; without intent, the disposition is unprincipled "whichever side is settled wins."**

This document **overwrites** the prior version of the audit (`9516dfc^:design/arch/facades/cranelisp-primitives-audit-s69.md`), which read the facade + lib.rs + Cargo.toml + FIXME 0212 but did not load Decision 0048's full body (esp §"Consequences" and §"Structural invariant — backend dep-ban"), Decision 0043 (the runtime split that placed the allocator inside `cranelisp-intrinsics`), Principle 7, Principle 8, Principle 15, Principle 18, or `bounded-contexts.md` §4a — and consequently mis-grounded F1 (correct conclusion, wrong rationale) and F4 (recommended Option 2 against an explicit Decision 0048 §"Consequences" `#[used]` prescription, with no flag that the Decision text must amend in lockstep). This re-author corrects the grounding and re-examines every disposition.

**Configuration loaded for this re-author.**

- `design/arch/principles.md` index + `principles/{07,08,15,18}.md` (full bodies)
- `design/arch/CLAUDE.md` (Decisions index + Baseline-diff discipline)
- `design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md` (binding source for this crate's shape) — full body including §"Consequences" and §"Structural invariant — backend dep-ban"
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` (the runtime split that placed the allocator inside `cranelisp-intrinsics`) — full body including §"Migration scope"
- `design/arch/decisions/0035-code-enum-integration-layer.md` (post-rollback canonical statement: GOT is the single source of truth for callable addresses)
- `design/arch/bounded-contexts.md` §4a (Primitives BC)
- `design/arch/fixmes/{0150,0157,0159,0161,0162,0182,0189,0191,0210,0212}-*.md` (every primitives-targeted FIXME in the active register)
- `design/arch/facades/primitives.md` (under audit)
- `crates/cranelisp-primitives/{Cargo.toml,public-api.txt,src/lib.rs}` (the as-built shape; sub-module `use` lines spot-checked for the intrinsics path)

---

## 0. Summary up front

`cranelisp-primitives` is the **cleanest crate in the workspace by pub-api volume**. Decision 0048's collapse of the published surface to one `pub static` + seven `pub mod`s is materially embodied — eight of the nine pub-api lines are submodule namespaces; the ninth is `PRIMITIVES_TABLE`. The "single item" intent of Decision 0048 is honoured at the type level (`LazyLock<Arc<SymbolTable<Code, ()>>>` matches the facade prescription exactly, modulo `cargo-public-api`'s full-path qualification).

What looked like an 11-finding audit in the prior version remains **eleven distinct findings** on re-grounded re-examination, but with **two prior dispositions flipped and one prior disposition rationale rewritten** because the architectural configuration tips them differently than the as-settled-side-wins reading did.

**Re-grounding makes the difference at:**

- **F1 (Cargo↔facade contradiction on intrinsics dep).** Prior verdict: facade-moves. **Re-grounded verdict: facade-moves, same direction, but the rationale flips.** The facade text "no intrinsics dep; allocator access goes through the linker-resolved name" is not a target-state the source has failed to reach — it is **stale facade text written without Decision 0043 in scope**. Decision 0043 §"Migration scope" explicitly placed the allocator inside `cranelisp-intrinsics`. The primitives crate's heap-allocating fns (`int-to-string`, `str-concat`, …) physically need allocator access; the Rust-path dep is the as-built shape AND is the structurally simplest acyclic edge per the workspace DAG. The facade text contradicts Decision 0043, not the source. The prior audit framed this as "the Rust-path form is also a Principle-15 advantage" — Principle 15 is about facade types living with their behaviour, not about how dep edges in `Cargo.toml` resolve. The correct citation is Principle 8 (no interim implementations of later-ring capabilities) + Decision 0043 §"Migration scope": the allocator's home is `cranelisp-intrinsics`; the path to call it is the Rust path; the linker-name shape was an alternative considered and not selected.

- **F4 (FIXME 0212 — `#[used]` discipline).** Prior verdict: **/arch arbitration recommended Option 2 (facade-moves) on Principle 7 + 18 + failure-loudness grounds**. **Re-grounded verdict: this is /design (primitives)' call (FIXME 0212 `target: /design (primitives)`), not /arch's. The recommendation flips to Option 1 (source-moves — add `#[used]` to the 45 fns) on the audit-discipline default ("source-moves to match facade when the facade is target-stating per Decision").** The grounding is direct: Decision 0048 §"Consequences" line "the ~22 individual `pub extern "C" fn` items demote to `pub(crate)` with `#[used]` discipline to prevent DCE." This is not facade prose alone — it is the Decision that authorised the facade prose. Treating it as facade drift (Option 2) requires Decision 0048 §"Consequences" to also amend in the same change-set; treating it as source drift (Option 1) is mechanical (45 single-line additions) and faithful to the binding Decision. The Principle 7 + 18 arguments for Option 2 are real but they are *change-the-Decision* arguments, not *the-facade-is-stale* arguments — they belong on a FIXME `target: /arch` proposing a Decision-0048 amendment, not on this audit's disposition. Per the audit-discipline default, the facade is target-stating and source moves to match.

- **F2 (sconcat placement).** Prior verdict: both-move. **Re-grounded verdict: facade-moves; the source-side question (extern_shims visibility) becomes a separate cross-crate audit observation, not a primitives-side action.** Reasoning: `spec/09-macros.md §9.7.3` clearly places `sconcat`'s `ModuleEntry` in the synthetic `macros` module, NOT in `primitives`. The facade's §"Marshalling" listing `sconcat` alongside `quote-sexp` under "Primitives inventory" is target-stating against the wrong target — the spec says `macros`, not `primitives`. Source is faithful to spec (the `extern_shims_harvest_covers_full_inventory` test carves `sconcat` out of `PRIMITIVES_TABLE` membership with an explicit prose comment citing `spec/09-macros.md`). Facade-moves: revise §"Marshalling" so `sconcat` is named as harvested-into-extern_shims-for-cross-module-consumption, not as a `PRIMITIVES_TABLE` member. The visibility question on `extern_shims()` is a downstream concern for the macros-module construction site's audit — surfaced as arbitration A2 *without* committing primitives-side to a visibility change.

The remaining dispositions stand:

- F3 (submodule pub-mod retention): facade-moves (descriptive → prescriptive). Grounded in Decision 0048's "single item" intent + Baseline-diff discipline.
- F5–F8: no action; alignment confirmations.
- F9–F11: coverage notes; no facade or source action.

**Disposition class counts (over 11 findings: F1–F11):**

| Class | Count | Meaning |
|---|---|---|
| Facade-moves | 4 (F1, F2, F3, +F4 was-here-now-flipped) → **3** | Facade text revised; source is faithful to Decisions/spec. |
| Source-moves | 1 (F4) | Add `#[used]` to 45 demoted fns; source-side delivery of binding Decision 0048 prose. |
| No action — alignment confirmed | 4 (F5, F6, F7, F8) | Source matches facade; audit records the check explicitly. |
| Coverage notes (informational) | 3 (F9, F10, F11) | Existing in-crate enforcement adequate; no facade or source action. |

**The audit's verdict**: SMALL DRIFT in count, **substantial in re-grounded rationale at F1 and F4**. The Cargo↔facade contradiction has been latent since the S68 close because the facade was authored without Decision 0043 in mind; closing it removes ambiguity for the workspace-DAG reader. The `#[used]` source-moves call closes FIXME 0212 in the direction of Decision 0048's binding prose; Principle 7 + 18 arguments for the alternative direction belong on a separate Decision-amendment FIXME if pursued.

---

## 1. Findings (per-item analysis, five blocks)

### Finding F1 — Cargo↔facade contradiction on `cranelisp-intrinsics` dep

**Facade expects.**

`design/arch/facades/primitives.md` §"Consumed surface" (lines 285–291):

> The primitives crate imports from:
> - **`cranelisp-types`** — the bulk of the dependency. […]
> - **`cranelisp-backend`** — for the `Code` type parameter on `SymbolTable<Code, ()>` AND for the `Code::Primitive` marker variant […]
>
> Primitives does NOT depend on `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-platform`, `cranelisp-intrinsics`, or `cranelisp` (binary). In particular: primitives does NOT depend on `cranelisp-intrinsics`. Where a primitive allocates heap (e.g., `int-to-string`), it does so by calling the allocator's extern fn at the linker-resolved name — the same way backend-emitted code calls intrinsics — not by depending on intrinsics as a Rust crate.

The facade is unambiguous: **no Rust-path dep on intrinsics**. The rationale offered is that allocator access goes through the linker-resolved-name path (the same path backend-emitted user code takes).

**Source does.**

`crates/cranelisp-primitives/Cargo.toml` line 8 carries `cranelisp-intrinsics = { path = "../cranelisp-intrinsics" }` — present and uncommented. The dep is exercised heavily across submodules:

- `src/bool.rs:8`: `use cranelisp_intrinsics::heap_string;`
- `src/bool.rs:21`: `use cranelisp_intrinsics::alloc;`
- `src/float.rs:8`: `use cranelisp_intrinsics::heap_string;` (and `alloc` at line 28)
- `src/int.rs:16-18`: `use cranelisp_intrinsics::alloc; use cranelisp_intrinsics::rc; use cranelisp_intrinsics::heap_string;`
- `src/string.rs:23-24`: `use cranelisp_intrinsics::{alloc, drop as drop_glue, rc}; use cranelisp_intrinsics::heap_string::{HeapString, alloc_string};`
- `src/string.rs:182`: `let vec_base = cranelisp_intrinsics::vec_runtime::vec_new(count);`
- `src/ring0.rs:42`: `use cranelisp_intrinsics::panic::runtime_panic;`

Not a backdoor; not a leaf reference — heap-allocating, RC-touching, drop-glue-emitting, and panic-emitting primitives reach into intrinsics by Rust path for the allocator, the RC tags, the drop functions, the heap-string allocator, the vec-runtime constructor, and the runtime-panic fn. Removing the dep would break compilation of `bool.rs`, `float.rs`, `int.rs`, `string.rs`, and `ring0.rs`.

**Design intent (grounded).**

Three loadings to settle, in cascade:

1. **Where the allocator lives.** Decision 0043 §"Migration scope" (the runtime split) is binding:
   > | Today (`cranelisp-runtime/src/`) | Goes to |
   > | […] |
   > | Allocator (Cat 2: `cranelisp_alloc` etc.) | **`cranelisp-intrinsics`** |
   > | `rc.rs` (Cat 2: RC inc/dec) | **`cranelisp-intrinsics`** |
   > | `drop.rs` (Cat 2: consume_*, drop glue) | **`cranelisp-intrinsics`** |
   > | `panic.rs` (Cat 2: `runtime_panic`) | **`cranelisp-intrinsics`** |
   The allocator is physically in `cranelisp-intrinsics`. Decision 0043 is `pre-implementation` at filing and has been progressively realised across S65 → S68; the as-built source already matches it.

2. **How primitives reach the allocator.** Decision 0043 §"Statement" places primitives as user-callable, ABI-stable, spec-defined; their bodies are Rust `extern "C"` fns. A heap-allocating primitive body is Rust code that needs to call an allocator — the Rust-path call (`cranelisp_intrinsics::alloc::alloc_with_rc(…)`) is the natural mechanism. Decision 0043 does **not** prescribe a linker-name resolution for this internal call; it prescribes linker-name resolution for **backend's emitted CLIF calls** to intrinsics (the codegen-layer ABI contract). Primitives' Rust bodies are not codegen output — they are static Rust functions whose binary is produced by `rustc`, then made available to the JIT/linker by `extern "C"` + `export_name`. Inside those bodies, the calling convention is whatever `rustc` resolves at compile time.

3. **What Decision 0048 says about the dep.** Decision 0048 §"Structural invariant — backend dep-ban" prescribes one specific dep-ban: `cranelisp-backend MUST NOT depend on cranelisp-primitives`. It says nothing about a primitives → intrinsics dep-ban. The §"Dep direction" subsection states: "`cranelisp-primitives → cranelisp-backend` is permitted […]. The reverse `cranelisp-backend → cranelisp-primitives` is forbidden." The facade text "primitives does NOT depend on cranelisp-intrinsics" is **not sourced from any Decision** — it is an unsourced facade-author claim.

**Grounded conclusion**: The facade text on the intrinsics dep is not target-stating per Decision; it is **stale facade text** — most likely authored in S67/S68 before Decision 0043's allocator placement had crystallised in the author's mind, with a rationale invented at write time (the "linker-resolved name" framing) that contradicts the as-built shape, the spec-of-record Decisions (43 + 48), and Principle 8 (no interim implementations — the Rust-path dep is the target shape, not a transitional form). No FIXME tracks "make primitives source achieve the no-intrinsics-dep target"; no Decision authorises that target.

**Difference implies.**

Three architectural questions are dispelled by the grounded reading:

1. **Which dep direction is the binding target?** The Rust-path dep is the binding target per Decisions 0043 + 0048 (no Decision forbids it; the workspace DAG is acyclic; the allocator must live in intrinsics and be callable from primitives). The "linker-resolved name" framing in the facade was an alternative the audit can now name as rejected.
2. **Is the dep edge acyclic?** Yes. `cranelisp-types` (leaf) ← `cranelisp-intrinsics` ← `cranelisp-primitives` (also depends on `cranelisp-backend`); `cranelisp-backend` depends on `cranelisp-intrinsics` and `cranelisp-types`, NOT on primitives. No cycle.
3. **What does the contradiction mean for the reader?** A reader of the facade learns (incorrectly) that primitives has zero Rust-path knowledge of intrinsics. Opening `int.rs`, `string.rs`, etc. confronts them with seven `use cranelisp_intrinsics::*;` lines. The contract documentation actively misleads.

**Disposition.**

**Facade moves.** The facade text §"Consumed surface" line 291 ("Primitives does NOT depend on `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-platform`, `cranelisp-intrinsics`, or `cranelisp` (binary). In particular: primitives does NOT depend on `cranelisp-intrinsics`. Where a primitive allocates heap …") is the target of revision.

Recommended replacement text (W2 work in `facades/primitives.md`):

```
- **`cranelisp-intrinsics`** — for the heap allocator (`alloc::alloc_with_rc`,
  `alloc::dealloc`), the RC tag operations (`rc::rc_inc`, `rc::rc_dec`), drop
  glue (`drop::*`), heap-string substrate (`heap_string::*`), the vec-runtime
  constructor (`vec_runtime::vec_new`), and `runtime_panic`. Decision 0043's
  §"Migration scope" placed these in `cranelisp-intrinsics`; primitives' heap-
  allocating, RC-touching, or panic-emitting bodies call them via Rust paths.
  The dep edge `cranelisp-primitives → cranelisp-intrinsics` is acyclic
  (intrinsics depends on types only, and primitives depends on types + intrinsics
  + backend; reverse edges are all forbidden by Decisions 0043 + 0048).

Primitives does NOT depend on `cranelisp-frontend`, `cranelisp-typecheck`,
`cranelisp-platform`, or `cranelisp` (binary). The backend dep is for the `Code`
type parameter on `SymbolTable<Code, ()>` and for the `Code::Primitive` marker
variant constructor; the reverse `cranelisp-backend → cranelisp-primitives` is
forbidden by Decision 0048 §"Structural invariant — backend dep-ban".
```

**Grounding citations**: Decision 0043 §"Migration scope" (allocator placement); Decision 0048 §"Structural invariant — backend dep-ban" (only dep-ban is backend → primitives, not primitives → intrinsics); Principle 8 (the Rust-path dep IS the target shape, not transitional).

**Source change: none.** The Cargo.toml comment block at lines 9–14 could optionally be extended to name the intrinsics edge alongside the backend one, but this is housekeeping, not S69 W2 work.

**Calibration vs prior audit**: same direction (facade-moves), substantively different rationale. Prior version cited Principle 15 + Principle-18-by-analogy; both citations were off-target. The correct citations are Decision 0043 + Decision 0048 (what no Decision forbids, no facade should claim is forbidden) + Principle 8 (no interim implementations).

---

### Finding F2 — `sconcat` placement: primitives vs synthetic `macros` module

**Facade expects.**

`design/arch/facades/primitives.md` §"Marshalling" (lines 139–146):

> #### Marshalling (submodule `marshal`)
>
> | Rust ident | Symbol name | Signature |
> |---|---|---|
> | `sconcat` | `sconcat` | `(i64, i64) -> i64` |
> | `quote_sexp` | `quote-sexp` | `(i64) -> i64` |
>
> User-callable from `defmacro` clause bodies per `spec/09-macros.md`.

The §"Primitives inventory" framing (line 92, immediately above the table groups) prescribes: "The following primitives are populated into `PRIMITIVES_TABLE` at static-init time." Read together: `sconcat` is asserted to land in `PRIMITIVES_TABLE`.

**Source does.**

`lib.rs:237` registers `sconcat` in the `extern_shims()` harvest:

```rust
m.insert("sconcat", marshal::sconcat as *const u8);
```

But the integration test at `lib.rs:391–414` (`extern_shims_harvest_covers_full_inventory`) explicitly carves `sconcat` out of `PRIMITIVES_TABLE` membership:

```rust
for name in extern_shims().keys() {
    assert!(
        PRIMITIVES_TABLE.get(name).is_some()
            || matches!(*name, "neq-i64" | "neq-f64" | "neq-bool" | "sconcat"),
        "shim {name} has no PRIMITIVES_TABLE entry"
    );
}
```

The test's prose comment (lines 397–403) explicitly names the rationale:
> `sconcat` — registered in the synthetic `macros` module per `spec/09-macros.md`, not in `primitives`.

`PRIMITIVES_TABLE` has no `sconcat` entry; `extern_shims()` does (for fn-ptr harvest, consumed by whatever site builds the `macros` module's `SymbolTable`).

**Design intent (grounded).**

Two binding sources for `sconcat`'s placement:

1. **`spec/09-macros.md` §9.7.3** (MEMORY-summarised; spec-of-record): "Sexp and SList types live in synthetic `macros` module (compiler-seeded, like `primitives`)." `sconcat` is one of the SList helpers that the prelude re-exports for `~@` (unquote-splicing) quasi-quote-generated code. Its `ModuleEntry` lives in `macros`, not in `primitives` — by spec.

2. **Decision 0048 §"Shape"** and `facades/primitives.md` §"Type shape" both define `PRIMITIVES_TABLE` as "the synthetic `primitives` module's symbol table and GOT." `sconcat`'s ModuleEntry belonging to `macros` (not `primitives`) means it cannot also be a `PRIMITIVES_TABLE` member — one entry, one module, per `bounded-contexts.md` §4a and the spec.

3. **Rust placement of the `extern "C" fn` body**: Rust placement is **independent of the `ModuleEntry` placement**. The `extern "C" fn` body lives physically in `cranelisp_primitives::marshal` because that crate is the codegen-detached single home for spec-defined extern fns (per Decision 0043's split). But its symbol-table entry — the user-facing Cranelisp-level binding — lives in the synthetic `macros` module. This is consistent with how `extern_shims()` is structured: it is the in-crate harvest of every extern fn ptr, regardless of which synthetic module's `SymbolTable` ultimately registers each fn ptr.

The facade's "Primitives inventory" table listing `sconcat` is therefore **target-stating against the wrong target**. Spec says `macros`; facade says `primitives`; source is faithful to spec.

**Difference implies.**

A reader of the facade who builds an inventory of `PRIMITIVES_TABLE.symbols` keys, comparing to the facade's tables, will find `sconcat` listed in the facade but absent from `PRIMITIVES_TABLE` at runtime. The inverse — looking up the `macros` module — would find `sconcat` there. The facade's accounting is wrong against spec.

The cross-module-harvest architectural claim hidden here: **`extern_shims()` is the single in-crate harvest because all `extern "C" fn` definitions physically live in the primitives crate, but the population it feeds is not exclusively primitives' GOT**. The `macros` module's `SymbolTable` construction site (which physically lives elsewhere — likely in `cranelisp-frontend` or in `int` macro-env wiring; not inspected by this primitives-narrow audit) must reach into primitives' harvest to obtain the `sconcat` fn ptr. This is a downstream cross-crate concern.

**Disposition.**

**Facade moves.** Split §"Marshalling" into two parts:

- `quote-sexp` — a true `PRIMITIVES_TABLE` member, callable as `primitives/quote-sexp`. Retain in the §"Primitives inventory" Marshalling subsection.
- `sconcat` — an `extern "C" fn` whose Rust body lives in `cranelisp-primitives::marshal::sconcat` AND whose fn-ptr is harvested into `extern_shims()` so that the synthetic `macros` module's `SymbolTable` (per `spec/09-macros.md`) can register it. Move to a new subsection §"Cross-module harvest items (Rust body in `cranelisp-primitives`, `ModuleEntry` elsewhere)" or annotate inline that `sconcat` is harvested-but-not-tabled-in-primitives. Cite `spec/09-macros.md` §9.7.3 as the binding placement.

**Grounding citations**: `spec/09-macros.md` §9.7.3 (`sconcat` lives in `macros` module); Decision 0048 §"Shape" (`PRIMITIVES_TABLE` is the `primitives` module's symbol table — by definition `sconcat`'s entry is not in it); `bounded-contexts.md` §4a (one entry, one module).

**Source change: none on facade-revision grounds.** The visibility of `extern_shims()` (currently private to lib.rs) is a separate cross-crate audit observation — surfaced as arbitration A2, NOT committed to as a primitives-side source change. Resolution requires inspecting the `macros` module construction site (the frontend or int audit's job, not primitives').

**Calibration vs prior audit**: prior version's disposition was "both move" with a source-side visibility reconfirmation slated. Re-grounded: facade-moves only; source is already faithful to spec. The visibility question is downstream cross-crate, not primitives-side.

---

### Finding F3 — Submodule `pub mod` retention as binding contract

**Facade expects.**

`design/arch/facades/primitives.md` §"Submodule pub-mod retention" (lines 243–255):

```
pub mod cranelisp_primitives::bool
pub mod cranelisp_primitives::float
pub mod cranelisp_primitives::int
pub mod cranelisp_primitives::marshal
pub mod cranelisp_primitives::ring0
pub mod cranelisp_primitives::string
pub mod cranelisp_primitives::vec
```

Surrounding prose (line 255):
> These remain `pub mod` for source organisation (and so `#[unsafe(export_name = "…")] pub(crate)` items can carry an `export_name` attribute — the `export_name` mechanism requires the fn be reachable from a `pub` path in the dependency graph for the symbol to land in the staticlib). Their members are `pub(crate)`; no `pub` extern fns reach consumers via Rust paths.

The section names the seven pub-mods but the framing is **descriptive** ("these remain `pub mod` for source organisation") rather than **prescriptive** ("these and only these may be `pub mod`"). The seven-ness of the set is implicit (the list is closed by enumeration) but unstated as an invariant.

**Source does.**

`crates/cranelisp-primitives/src/lib.rs:60–66`:

```rust
pub mod bool;
pub mod float;
pub mod int;
pub mod marshal;
pub mod ring0;
pub mod string;
pub mod vec;
```

Seven `pub mod` lines, alphabetical, matching the baseline exactly (`public-api.txt:2–8`). No drift.

**Design intent (grounded).**

Decision 0048's binding intent is "single item public API" — `PRIMITIVES_TABLE` is the one item. The seven `pub mod`s are the **named exception** required for `#[unsafe(export_name = "…")] pub(crate) extern "C" fn` reachability (the `export_name` mechanism's structural requirement, per the facade prose). The "single item" framing implies the seven are a closed exception set, not an open extension point — every additional `pub mod` is silent surface growth at the only axis the public-api baseline is set up to absorb.

The Baseline-diff discipline (`design/arch/CLAUDE.md`) is the supporting mechanism: every facade compliance test asserts every baseline line is named in the corresponding facade. For the seven-ness to be enforced, the facade text MUST prescriptively name "exactly these seven, no more"; otherwise a contributor adding an eighth pub-mod in source + an eighth line in the facade in the same change-set produces facade-and-baseline-agree state, the compliance test passes, and the silent surface growth lands without an explicit Decision-level review.

**Difference implies.**

The user's challenge (per Sprint 69 task brief): "a new `pub mod` line would slip through." Today's defence is: the compliance test catches deletion well (delete a pub-mod → baseline shrinks → facade still lists seven → mismatch → fail), but for addition it catches only when the facade is NOT updated. The descriptive framing leaves no contract-level pointer for the eighth-pub-mod-attempting contributor to point at and rejected — the prose says "for source organisation" which a determined contributor can extend.

The categorical line Decision 0048 draws is "single public API item." The seven pub-mods are the named structural exception. An eighth is a new exception — requires explicit Decision-level review, not silent acceptance.

**Disposition.**

**Facade moves.** Convert §"Submodule pub-mod retention" from descriptive to prescriptive. Recommended replacement text (W2 work in `facades/primitives.md`):

> The public-api of `cranelisp-primitives` MUST contain exactly the following seven `pub mod` lines (plus the universal `pub mod cranelisp_primitives` crate-root line emitted by `cargo-public-api` for every crate):
>
> ```
> pub mod cranelisp_primitives::bool
> pub mod cranelisp_primitives::float
> pub mod cranelisp_primitives::int
> pub mod cranelisp_primitives::marshal
> pub mod cranelisp_primitives::ring0
> pub mod cranelisp_primitives::string
> pub mod cranelisp_primitives::vec
> ```
>
> Any additional `pub mod` line is a facade violation. New primitive categories MUST fit one of the seven existing sub-modules. Adding an eighth requires a Decision-level change (filed via `/arch`) on whether the categorical line Decision 0048 draws should grow; the facade compliance test catches silent growth via baseline-vs-facade-list mismatch.
>
> Why pub-mod retention exists at all (the seven are not the empty set): `#[unsafe(export_name = "…")] pub(crate) extern "C" fn` requires the fn be reachable from a `pub` path in the dependency graph for the symbol to land in the staticlib's exported symbol table. The seven `pub mod` lines are the minimum needed to keep the ~45 extern fns reachable for `export_name` purposes. Without `pub mod`, the extern would be DCE'd in `--link` mode (and unreachable at the `as *const u8` cast in `extern_shims()`, breaking the JIT-mode path too).

**Grounding citations**: Decision 0048 §"Shape" + §"Consequences" ("`cranelisp-primitives`' published Rust API collapses to one item"); Baseline-diff discipline (`design/arch/CLAUDE.md`); Principle 8 (the seven-pub-mod set is the target shape, not transitional).

**Source change: none.** Source is already faithful to the closed set.

**Calibration vs prior audit**: same direction and substance (facade-moves, descriptive → prescriptive). No change.

---

### Finding F4 — FIXME 0212: `#[used]` discipline (re-grounded — disposition FLIPPED)

**Facade expects.**

`design/arch/facades/primitives.md` §"Public surface" (lines 20–22):

> The ~22 individual extern fns demote to `pub(crate) extern "C"` with `#[used]` discipline (to prevent DCE in `--link`-mode static archives).

§"Removed from pub surface" (line 180): "Demoted from `pub` to `pub(crate)` with `#[used]` discipline (22 items)" — explicit heading.

**Source does.**

The ~45 demoted fns (count grew from the facade's stale ~22 figure during S67's string-physical-relocation, acknowledged parenthetically in the facade line 230) carry `#[unsafe(export_name = "…")]` but **do NOT carry `#[used]`**. The DCE-prevention mechanism that actually keeps them linkable is `extern_shims()` at `lib.rs:198–261` — each fn is referenced as `fn as *const u8` and stored in a `HashMap<&'static str, *const u8>` that the `LazyLock`-initialised `PRIMITIVES_TABLE` consumes. The static-data reference (the `LazyLock` is `'static`) provides DCE protection through the standard "no static data reference → DCE candidate" logic.

Wave 6 verification at S68 close: `--link` mode end-to-end works; the live binary contains all 45 extern symbols in its `.symtab`. Source is functionally correct.

**Design intent (grounded).**

The binding source is **Decision 0048 §"Consequences"**, line 124:

> `cranelisp-primitives`' published Rust API collapses to one item (`PRIMITIVES_TABLE`); the ~22 individual `pub extern "C" fn` items demote to `pub(crate)` with `#[used]` discipline to prevent DCE.

The facade's `#[used]` prose is sourced. **Decision 0048 names `#[used]` as the canonical mechanism, not as facade convenience text.**

FIXME 0212's text says "Either resolution is acceptable" — but FIXME 0212 is a Wave 6 `/review`-filed gap report, not a Decision-amending document. Its "either is acceptable" framing reflects the filing reviewer's view at S68 close that runtime correctness is not at stake; it does not arbitrate the architectural canonical form. Per the audit-discipline default ("source-moves to match facade when the facade is target-stating per Decision"), the facade is target-stating because Decision 0048 §"Consequences" is target-stating; source moves to match.

The Principle 7 + 18 arguments for the alternative direction (Option 2 — make `extern_shims()` the canonical mechanism) are real and weight-bearing, but they are **arguments to amend Decision 0048**, not arguments that the facade is stale. The correct cascade for adopting Option 2 is: file a new FIXME `target: /arch` proposing a Decision 0048 §"Consequences" amendment that retires `#[used]` in favour of `extern_shims()`, run that through /arch review, and only then revise the facade. That is a separate piece of work the audit can recommend but cannot itself execute (it would amount to /design overriding /arch's binding Decision text).

**Difference implies.**

This is a **binary architectural choice between two DCE-prevention disciplines** — but it is no longer a /arch arbitration in the audit; it is **/design (primitives)' call**, because FIXME 0212 targets `/design (primitives)`. The two options:

- **Option 1 — `#[used]` on every demoted fn (source-moves; faithful to Decision 0048 §"Consequences").** Add `#[used]` to each of the 45 `pub(crate) extern "C" fn` items. ~45 single-line additions across 7 files. Belt-and-suspenders with `extern_shims()` — defence in depth.
- **Option 2 — `extern_shims()` as canonical (requires Decision 0048 amendment, then facade-moves).** Decision 0048 §"Consequences" amends to drop `#[used]` text; facade follows; FIXME 0212 closes. Mechanically simpler at the source layer (zero source change), but requires /arch arbitration to amend the binding Decision.

The audit-discipline default selects Option 1 when no other consideration overrides:

- **The facade IS the binding intent** (Decision 0048 grounds it).
- **"Facade moves" is correct only when the facade is genuinely stale** (a later Decision retracted, or source has evolved past). Neither applies here: no later Decision retracts the `#[used]` prescription; source has not evolved past it (source simply hasn't reached it).
- **Deferral is acceptable only AFTER the disposition is named** — schedule, not avoidance.

The Principle 7 + 18 arguments for Option 2 are real:
- **Principle 7 (single source of truth)**: one mechanism (`extern_shims()`) for one invariant (DCE prevention).
- **Principle 18 (structurally enforce)**: the in-crate test `extern_shims_harvest_covers_full_inventory` enforces "every harvested name has a place to land", a structural property of the workspace.
- **Failure-loudness**: Option 2 fails uniformly across both modes; Option 1 has a "works in --link, broken in JIT" failure mode if the contributor adds `#[used]` but forgets `extern_shims()`.

These arguments support a /arch FIXME proposing a Decision 0048 amendment. They do NOT support flipping the audit's disposition to "facade-moves" without that amendment — that would put the audit in the position of overriding Decision 0048 §"Consequences" text on its own authority. Per Sprint 69 user direction:

> "a 'facade moves' recommendation against a target-stating facade actively undoes the architectural progression."

Decision 0048's `#[used]` prescription IS target-stating. The disposition flips to source-moves.

**Disposition.**

**Source moves.** `/dev (primitives)` adds `#[used]` to each of the ~45 `pub(crate) extern "C" fn` items across `crates/cranelisp-primitives/src/{ring0,bool,int,float,marshal,string,vec}.rs`. FIXME 0212 closes on the merge of the source change with a one-line note:

> Resolved Option 1 per cranelisp-primitives-audit-s69 §F4 — faithful to Decision 0048 §"Consequences". `#[used]` is the canonical DCE-prevention mechanism per the binding Decision; `extern_shims()` continues to provide belt-and-suspenders coverage and the harvest-completeness test. Option 2 (retire `#[used]` in favour of `extern_shims()`-only) was considered and rejected as outside this audit's authority — it would require a /arch-filed amendment of Decision 0048 §"Consequences", not a /design (primitives) facade revision.

**Optional follow-on (not blocking F4 closure)**: `/design (primitives)` MAY file a new FIXME `target: /arch` proposing Decision 0048 §"Consequences" amend to retire `#[used]` per Principle 7 + 18 + failure-loudness. If /arch arbitrates for the amendment, Option 2 lands as a S70+ cascade: amend Decision 0048; revise the facade; remove the 45 `#[used]` attributes; close the FIXME. The audit RECOMMENDS this follow-on as net-architectural-cleanup but it is independent of F4's S69 closure.

**Grounding citations**: Decision 0048 §"Consequences" (the `#[used]` prescription); audit-discipline default ("source-moves to match facade when the facade is target-stating per Decision"); Sprint 69 user direction (the regression-mechanism risk of "facade-moves against target-stating facade").

**Calibration vs prior audit (FLIPPED)**:

| Aspect | Prior audit | Re-grounded audit |
|---|---|---|
| Disposition | /arch arbitration → recommend Option 2 (facade-moves) | Source-moves (Option 1); Option 2 → optional follow-on FIXME `target: /arch` |
| Rationale | Principle 7 + 18 + failure-loudness → facade is overcommitted; retire `#[used]` | Decision 0048 §"Consequences" is target-stating; Principle 7/18 args belong on a Decision-amendment FIXME, not on the audit disposition |
| Authority | /arch (per A1 arbitration brief) | /design (primitives) — FIXME 0212 targets /design; the call is /design's to make per audit-discipline default |
| Cascade | 2 facade edits + 1 Decision-text edit | 45 source-attribute additions across 7 files |

This is the most consequential flip in this re-author. The prior version recommended overriding Decision 0048 §"Consequences" on Principle-grounds without filing the Decision-amendment FIXME first; the re-grounded version respects the Decision text and routes the Principle-driven optimisation through the proper /arch channel.

---

### Finding F5 — `PRIMITIVES_TABLE` shape conformity to Decision 0048 post-amendment

**Facade expects.**

`design/arch/facades/primitives.md` §"Type shape" line 18 + lines 27–53:

```rust
/// Statically-constructed symbol table + GOT for the synthetic `primitives` module.
/// `Arc<SymbolTable<Code, ()>>` Arc-cloned into every `CompilerSession` at startup.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>;
```

Type parameters: `SymbolTable<Code, ()>` where `Code` is the post-S68-amendment `cranelisp_backend::Code` enum with the marker variant `Code::Primitive` (no payload).

Population intent (lines 56–69): one `ModuleEntry::Def` per primitive, each with `code: Some(Code::Primitive)`, `got_slot: Some(N)`, `kind: DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, jit_name: Some(JitSymbol::from(name)) }`, `visibility: Visibility::Public`.

**Source does.**

`public-api.txt` line 9:

```
pub static cranelisp_primitives::PRIMITIVES_TABLE: std::sync::lazy_lock::LazyLock<alloc::sync::Arc<cranelisp_types::module::SymbolTable<cranelisp_backend::code::Code, ()>>>
```

Matches the facade-prescribed shape modulo `cargo-public-api`'s full-path qualification (`std::sync::lazy_lock::LazyLock`, `alloc::sync::Arc`, etc.).

Population at `lib.rs:120–151` (`insert_primitive_entry`): every field set matches the facade prescription. In-crate test `every_entry_carries_code_primitive_marker` (`lib.rs:331–349`) asserts `code: Some(Code::Primitive)` on every entry. In-crate test `every_entry_carries_got_slot` (`lib.rs:318–329`) asserts `got_slot.is_some()` on every entry.

**Design intent (grounded).**

Three confirmation points from the binding sources:

1. **`Arc` wrapper present.** Decision 0048 §"Shape" prescribes `LazyLock<Arc<SymbolTable<Code, ()>>>`. Source matches.
2. **`C = Code` type parameter.** Required for the marker variant to be expressible at all per Decision 0048 (A2 amendment 2026-05-17). CompilerSession can Arc-clone into `SymbolTables<Code, ()>` without type-erasure.
3. **`Code::Primitive` marker on every entry.** Decision 0048 (A2 amendment) prescribes the marker; source enforces via in-crate test; pub-api does not (and cannot) expose runtime contents.

All three are aligned. No drift.

**Difference implies.**

Audit-side check confirms Decision 0048's binding shape is met by source. A reader doing a literal string compare between facade prose and pub-api line 9 will see path-qualification differences (this is normal `cargo-public-api` behaviour, handled by the facade compliance test's matching layer).

**Disposition.**

**No action — alignment confirmed.** Recorded as F5 so future audits do not re-discover the alignment. The Decision 0048 §"Shape" post-amendment requirements are met by source.

**Grounding citations**: Decision 0048 §"Shape" + (A2) amendment.

**Calibration vs prior audit**: same disposition; rationale identical. No change.

---

### Finding F6 — Hidden surface: `not` primitive (Decision 0048 (C1) closure)

**Facade expects.**

`design/arch/facades/primitives.md` §"Ring-0 arithmetic + comparison" row line 120: `not` is listed as a Ring-0 primitive (kebab-case `not`, signature `(i64) -> i64`). Annotation: "**NEW S68** per Decision 0048 (C1), closes FIXME 0157". §"Removed from pub surface" line 203 confirms `cranelisp_primitives::ring0::not` is `pub(crate) extern "C" fn` from authoring (never `pub`).

**Source does.**

`lib.rs:222`: `m.insert("not", ring0::not as *const u8);`

Registered in `extern_shims()`; populated into `PRIMITIVES_TABLE` via the `ring0_primitives()` registry union. In-crate test `not_primitive_present_and_callable` (`lib.rs:371–389`) verifies `PRIMITIVES_TABLE.get("not").is_some()` AND that the GOT slot's fn-ptr is callable with the expected semantics (`not(0) == 1`, `not(1) == 0`).

Absent from `public-api.txt` (correct — `pub(crate) extern "C" fn` is internal).

**Design intent (grounded).**

Decision 0048 (C1) and `spec/appendix-a-builtins.md:79` (`not` as primitive). FIXME 0157 (`/design (primitives)` filed by `/dev (primitives)`) closed at S68 close per the facade annotation.

**Difference implies.**

No drift. The `not` primitive is correctly registered, callable, and absent from the published surface per the post-S68 narrowing.

**Disposition.**

**No action — alignment confirmed.** Confirms FIXME 0157 closure landed correctly.

**Grounding citations**: Decision 0048 (C1); `spec/appendix-a-builtins.md` §A.3.

**Calibration vs prior audit**: same disposition. No change.

---

### Finding F7 — Inventory cardinality: full 45-entry harvest

**Facade expects.**

`design/arch/facades/primitives.md` §"Primitives inventory" tables (lines 96–174):
- Ring 0 arithmetic + comparison: 23 entries
- Primitive type conversions: 4 entries
- Marshalling: 2 entries (see F2 caveat on `sconcat`)
- String operations: 15 entries
- Vec query: 1 entry

Total: **45 entries** in `extern_shims()`; ~41 of them (45 minus `neq-i64`, `neq-f64`, `neq-bool`, `sconcat`) appear in `PRIMITIVES_TABLE.symbols`.

**Source does.**

`lib.rs:198–261` registers 45 entries; counted by category, all rows match. In-crate test `primitives_table_is_non_empty_with_expected_minimum` (`lib.rs:301–316`) asserts `PRIMITIVES_TABLE.symbols.len() >= 30` — intentionally loose floor.

**Design intent (grounded).**

The exact-count contract is intentionally NOT in the in-crate test — Decision 0048's intent is that primitive cardinality is governed by **spec conformance tests** (`/qa`), not by `cargo-public-api` or in-crate harvest tests. Per `facades/primitives.md` §"Versioning policy":

> The **semantic surface** (which primitives exist + their signatures) is governed by **spec conformance tests** (`/qa`), NOT by `cargo-public-api`.

The loose floor of ≥30 is intentional to absorb spec-driven primitive churn without requiring this test to track an exact count. Brittle exact-count tracking would tie this test to every primitive addition (the kind of fragility Decision 0048 explicitly designs against).

**Difference implies.**

The prior audit framed "facade lists ~44; source has 45" as an inventory drift — re-examined, this was a counting artefact. The facade footnote at line 230 explicitly acknowledges "the exact count is ~45 including `not`". Both name 45 in their accounting. No drift.

**Disposition.**

**No action — alignment confirmed.** The 45-entry inventory matches. The loose floor is documented and intentional. The audit notes the loose floor as informational, not as a coverage hole — exact-count tracking would tie the in-crate test to every primitive addition, undermining Decision 0048's "spec conformance is the binding inventory layer" framing.

**Grounding citations**: Decision 0048 §"Versioning policy" via `facades/primitives.md` §"Versioning policy"; `bounded-contexts.md` §4a (spec-driven evolution).

**Calibration vs prior audit**: same disposition (no action); rationale unchanged.

---

### Finding F8 — Unannounced surface: crate-root `pub mod cranelisp_primitives` line

**Facade expects.**

The facade does not name `pub mod cranelisp_primitives` (the crate-root emission) anywhere. The §"Public surface" framing of "one item" implies the public surface is one symbol; the seven sub-mod lines are named in §"Submodule pub-mod retention"; the crate root is silent.

**Source does.**

`public-api.txt:1`: `pub mod cranelisp_primitives`. Standard `cargo-public-api` crate-root emission. Every Rust crate's pub-api begins with this line.

**Design intent (grounded).**

Decision 0048 has no body on the crate-root line — it cannot, because the line is a universal `cargo-public-api` emission unrelated to the facade's contractual surface. The Baseline-diff discipline (`design/arch/CLAUDE.md`) treats it as a mechanical test-side concern, not a facade-bound surface.

**Difference implies.**

Universal pub-api emission for any Rust crate. Not a binding-contract surface; not a drift.

**Disposition.**

**No action — universal emission.** Recorded as F8 because every pub-api line is named in the audit; the crate-root line is the one universal emission that does not need facade text. `/qa` may add a comment to the facade compliance test naming "the crate-root `pub mod {crate}` line is universal and not facade-bound" if reviewer feedback suggests the silence is confusing — but this is auto-trait noise.

**Grounding citations**: `cargo-public-api` emission convention (universal); Baseline-diff discipline.

**Calibration vs prior audit**: same disposition; no change.

---

### Finding F9 — Coverage hole: `Code::Primitive` marker invariant at workspace tier

**Facade expects.**

Per Decision 0048 §"Shape" (lines 25–32 of the Decision) and `facades/primitives.md` §"Static-init contract" (lines 56–69): every `ModuleEntry::Def.code = Some(Code::Primitive)` in `PRIMITIVES_TABLE`. The invariant is binding for the lifecycle-category-as-grep-able-marker rationale Decision 0048 (A2 amendment) names — pattern-matchers over `Code` get a third arm that is purely descriptive; no resource handling.

**Source does.**

In-crate test `every_entry_carries_code_primitive_marker` (`lib.rs:331–349`) enforces the invariant. Runs in primitives' own test binary (`cargo nt -p cranelisp-primitives`). The 3 workspace-tier mechanical tests (`facade_compliance.rs`, `facade_pif_rows.rs`, `public_api_relocations.rs`) do not assert this invariant; they cannot, since `PRIMITIVES_TABLE`'s runtime contents are not introspectable from outside the crate without exposing introspection surface.

**Design intent (grounded).**

Principle 7 (single source of truth) + Principle 18 (enforce structurally) jointly select the in-crate test tier: the invariant lives where the construction does (lib.rs's `insert_primitive_entry`), so the test that asserts the invariant should live next door. Exporting introspection surface to workspace tier to fix a single-tier coverage gap would be a net public-surface increase — Decision 0048 explicitly designs against this.

**Difference implies.**

Coverage is adequate at the in-crate tier. A future refactor that bypassed `insert_primitive_entry` would not be caught by workspace-tier tests — but it would be caught by the in-crate test, which runs on every `cargo nt -p cranelisp-primitives`. The single-tier coverage is defensible.

**Disposition.**

**No facade or source action; `/qa` coverage note.** The in-crate test is the right tier per Principle 7 + 18. Audit records the single-tier coverage so `/qa`'s Wave 2 inventory has the test on its always-run set.

**Grounding citations**: Decision 0048 §"Shape" (the invariant); Principle 7 (single home for the invariant); Principle 18 (in-crate test is the structural enforcement).

**Calibration vs prior audit**: same disposition; rationale identical.

---

### Finding F10 — Coverage hole: GOT-slot population invariant at workspace tier

**Facade expects.**

Per Decision 0048 §"Static-init contract" (`facades/primitives.md` lines 56–69): every entry's `got_slot` is `Some(N)` and the corresponding GOT slot is populated with the harvested fn-ptr at static-init time.

**Source does.**

In-crate test `got_slots_hold_extern_ptrs_for_harvested_shims` (`lib.rs:351–369`) enforces this. Same single-tier coverage shape as F9.

**Design intent (grounded).**

Decision 0035 ("GOT is the single source of truth for callable addresses; no per-entry pointer field") + Decision 0048 §"Static-init contract" jointly prescribe the GOT-slot-population invariant. Same tier-selection argument as F9.

**Difference implies.**

Symmetric to F9 — adequately covered at the in-crate tier; not surfaced to workspace tier; tier choice defensible.

**Disposition.**

**No facade or source action; `/qa` coverage note.** Same as F9. The two coverage holes are symmetric; the same `/qa` Wave 2 inventory comment covers both.

**Grounding citations**: Decision 0035 (GOT is single source of truth); Decision 0048 §"Static-init contract"; Principles 7 + 18.

**Calibration vs prior audit**: same disposition; rationale identical.

---

### Finding F11 — Coverage hole: dep-ban test symmetry

**Facade expects.**

`design/arch/facades/primitives.md` §"Consumed surface" lines 289–290: the dep-ban is one-direction — `cranelisp-backend MUST NOT depend on cranelisp-primitives`. The reverse edge `cranelisp-primitives → cranelisp-backend` is permitted (required, for `Code::Primitive`).

**Source does.**

`crates/cranelisp-backend/tests/no_primitives_dep.rs` exists (66 LOC). Reads `crates/cranelisp-backend/Cargo.toml` via `env!("CARGO_MANIFEST_DIR")` and asserts the manifest does not contain the substring `cranelisp-primitives`. Test name: `s68_backend_does_not_depend_on_primitives`. Lives at the backend's crate tier per the test's doc comment.

The forward edge `primitives → backend` has no symmetric "presence" test — `cranelisp-primitives/Cargo.toml:15` lists `cranelisp-backend` (verified) but no test asserts it remains.

**Design intent (grounded).**

Decision 0048 §"Structural invariant — backend dep-ban" prescribes the **one-direction** ban: `cranelisp-backend → cranelisp-primitives` is forbidden. The forward edge `cranelisp-primitives → cranelisp-backend` is **permitted** (not required by name in any test) — it carries the `Code::Primitive` import. Principle 18 §"Workspace dep-bans": the structural mechanism enforces the forbidden direction at every `cargo build`; the permitted direction is the absence of a constraint, structurally enforced by the workspace DAG being acyclic.

The audit's prior C3 finding ("no workspace-tier dep-ban test") was wrong — the test exists. The symmetric "presence" test for the forward edge would catch a contributor accidentally removing the backend dep from primitives (which would break `Code::Primitive` import). That failure would surface at compile time (the `use cranelisp_backend::Code;` line at `lib.rs:54` would fail to resolve) — Principle 18's structural enforcement covers it without a dedicated test.

**Difference implies.**

The prior audit's C3 was incorrect (test exists). The symmetric-test gap is real but not structurally significant: a missing forward edge surfaces at compile time as a Rust error, not as a silent dispatch divergence. Belt-and-suspenders only.

**Disposition.**

**No facade or source action.** The one-direction dep-ban is adequately enforced by `no_primitives_dep.rs`. The symmetric presence test is **not recommended** — Principle 18's structural enforcement (compile-time error on missing `Code` import) covers the failure mode without a dedicated test surface.

`/qa` may consider adding `crates/cranelisp-primitives/tests/has_backend_dep.rs` (~20 LOC mirror) as belt-and-suspenders in S70+, but it is not blocking and not load-bearing.

**Grounding citations**: Decision 0048 §"Structural invariant — backend dep-ban"; Principle 18 §"Workspace dep-bans".

**Calibration vs prior audit**: prior recommended adding the symmetric test as "optional" with `/qa` referral. Re-grounded: the symmetric test is unnecessary because Principle 18 covers the failure mode structurally (compile-time error). No source-side optional addition.

---

## 2. Findings overview

| ID | Subject | Disposition | Grounding citation |
|---|---|---|---|
| F1 | Cargo↔facade contradiction on `cranelisp-intrinsics` dep | Facade moves | Decision 0043 §"Migration scope"; Decision 0048 §"Structural invariant — backend dep-ban" (the only dep-ban named); Principle 8 |
| F2 | `sconcat` placement: primitives vs synthetic `macros` module | Facade moves; A2 arbitration deferred to consuming-site audit | `spec/09-macros.md` §9.7.3; Decision 0048 §"Shape"; `bounded-contexts.md` §4a |
| F3 | Submodule `pub mod` retention as binding contract | Facade moves (descriptive → prescriptive) | Decision 0048 §"Shape" + §"Consequences"; Baseline-diff discipline; Principle 8 |
| F4 | FIXME 0212: `#[used]` discipline | **Source moves** (FLIPPED from prior) | Decision 0048 §"Consequences" (the binding `#[used]` prescription); audit-discipline default |
| F5 | `PRIMITIVES_TABLE` shape conformity | No action — alignment confirmed | Decision 0048 §"Shape" + (A2) amendment |
| F6 | `not` primitive (Decision 0048 (C1) closure) | No action — alignment confirmed | Decision 0048 (C1); `spec/appendix-a-builtins.md` §A.3; FIXME 0157 closure |
| F7 | Inventory cardinality: 45-entry harvest | No action — alignment confirmed | `facades/primitives.md` §"Versioning policy"; `bounded-contexts.md` §4a |
| F8 | Crate-root `pub mod cranelisp_primitives` line | No action — universal emission | `cargo-public-api` emission convention |
| F9 | `Code::Primitive` marker invariant at workspace tier | No action; `/qa` coverage note | Decision 0048 §"Shape"; Principles 7 + 18 |
| F10 | GOT-slot population invariant at workspace tier | No action; `/qa` coverage note | Decision 0035; Decision 0048 §"Static-init contract"; Principles 7 + 18 |
| F11 | Dep-ban test symmetry | No action (prior "optional" REVISED to "unnecessary") | Decision 0048 §"Structural invariant — backend dep-ban"; Principle 18 |

**Disposition class totals**: Facade moves: 3 (F1, F2, F3). Source moves: 1 (F4). No action / alignment confirmed: 4 (F5, F6, F7, F8). Coverage notes: 2 (F9, F10). No action revised: 1 (F11).

---

## 3. Calibration: prior dispositions before and after grounding

| Finding | Prior disposition | Re-grounded disposition | Flipped? | Most consequential change |
|---|---|---|---|---|
| F1 | Facade moves; rationale: Principle 15 + Principle-18-by-analogy | Facade moves; rationale: Decision 0043 §"Migration scope" + Decision 0048 §"Structural invariant" + Principle 8 | Rationale flipped, direction same | Grounding moves from off-target Principle-15 citation to the correct Decision-pair citation; future readers can trace the as-built dep to Decision 0043's explicit migration |
| F2 | Both move (facade + source visibility re-confirmation) | Facade moves; source visibility question = downstream cross-crate concern (arbitration A2) | Disposition flipped (both-move → facade-moves) | Source is faithful to spec (`spec/09-macros.md` §9.7.3); the visibility question is the macros-module construction site's problem, not primitives'. Removing the source-side commitment closes a phantom S69 W2 source-side action item |
| F3 | Facade moves (descriptive → prescriptive) | Facade moves (descriptive → prescriptive) | No flip | Same |
| F4 | /arch arbitration → Option 2 recommended (facade-moves: retire `#[used]`) | **Source moves (Option 1): add `#[used]` to 45 fns** | **Disposition flipped (facade-moves → source-moves)** | **The most consequential flip.** Decision 0048 §"Consequences" explicitly names `#[used]` as the canonical mechanism. The prior audit recommended overriding the Decision text on Principle-grounds without filing a Decision-amendment FIXME first — that is the "facade-moves against target-stating facade" regression the discipline forbids. Source moves to deliver the binding Decision text; optional follow-on FIXME `target: /arch` proposes amending Decision 0048 if Principle 7+18 weight is judged sufficient |
| F5 | No action — alignment confirmed | No action — alignment confirmed | No flip | Same |
| F6 | No action — alignment confirmed | No action — alignment confirmed | No flip | Same |
| F7 | No action — alignment confirmed; "facade lists ~44; source has 45" retraction | No action — alignment confirmed | No flip | Same |
| F8 | No action — universal emission | No action — universal emission | No flip | Same |
| F9 | No action; `/qa` coverage note | No action; `/qa` coverage note | No flip | Same |
| F10 | No action; `/qa` coverage note | No action; `/qa` coverage note | No flip | Same |
| F11 | Optional source-side symmetric test (surface to `/qa`) | **No action; symmetric test unnecessary per Principle 18** | Recommendation flipped (optional add → not recommended) | Principle 18 covers the forward-edge failure mode at compile time; a symmetric test is belt-and-suspenders that does not earn its keep |

**Flipped dispositions: 3 (F2 disposition; F4 disposition; F11 recommendation).**
**Rationale-flipped only: 1 (F1).**
**Most consequential flip: F4** — the prior audit's recommendation to override Decision 0048 §"Consequences" on Principle 7+18 grounds without filing a Decision-amendment FIXME first was the regression-mechanism risk the audit-discipline default explicitly prohibits.

---

## 4. Arbitration briefs (genuinely unsourced; require cross-skill input)

### Arbitration A1 — Decision 0048 §"Consequences" `#[used]` retire? (optional follow-on to F4)

**Question.** Should Decision 0048 §"Consequences" amend to retire the `#[used]` prescription in favour of `extern_shims()` as the canonical DCE-prevention mechanism (Principle 7 + 18 + failure-loudness grounds)?

**Stakeholders.** `/arch` (authority on Decision 0048 text); `/design (primitives)` (filer if pursued); `/dev (primitives)` (45-fn revert if amended).

**Note.** This is the audit's **optional follow-on** recommendation, NOT a blocking arbitration. F4 closes in S69 via source-moves (Option 1) regardless of A1. A1 is the path to Option 2 if its architectural merit is judged sufficient on independent grounds.

**Evidence toward retiring `#[used]`.**
- **Principle 7 (single source of truth)**: one mechanism (`extern_shims()` static-data references) for one invariant (DCE prevention).
- **Principle 18 (structural enforcement)**: `extern_shims_harvest_covers_full_inventory` in-crate test structurally enforces "every harvested name has a place to land" — a stronger property than the per-attribute `#[used]` discipline.
- **Failure loudness**: missing-from-`extern_shims()` is loud in both `--link` and JIT modes (DCE in `--link`; GOT slot not populated in JIT). Missing `#[used]` only is silent in `--link` if `extern_shims()` happens to keep the fn linked; partial-state mismatches between the two mechanisms are possible.
- **No rotting attribute surface**: every new primitive MUST be added to `extern_shims()` to be callable; under Option 2 there is one place to maintain.

**Evidence toward keeping `#[used]`.**
- **Faithful to current Decision 0048 §"Consequences"** — Rust-idiomatic mechanism for "do not DCE this".
- **Belt-and-suspenders**: defence in depth. If a future refactor accidentally removes a fn from `extern_shims()`, the `#[used]` attribute keeps the fn in the staticlib for `--link` mode (the failure mode becomes "primitive in binary but unreachable via GOT", arguably more debug-able than "primitive missing entirely").
- **Bounded change**: 45 single-line additions; mechanical.

**What tips the choice.** `/arch`'s call on whether the architectural-cleanliness gain (Option 2) is worth the binding-Decision amendment + 45-fn revert work. The audit does not arbitrate this — F4's source-moves closes the FIXME 0212 gap on Decision 0048's binding text first; A1 is the optional cleanup.

**Concrete next step.** `/design (primitives)` files a new FIXME `target: /arch` with this brief embedded (if pursued). `/arch` evaluates per Principle 7 + 18 weight vs the precedent of binding-Decision-text stability.

---

### Arbitration A2 — `sconcat` cross-module wiring (downstream from F2)

**Question.** Where is the synthetic `macros` module's `SymbolTable` constructed, and how does it obtain the `sconcat` fn-ptr from `cranelisp-primitives::marshal::sconcat`?

**Stakeholders.** `/design (frontend)` or `/design (int)` (likely owner of the macros-module construction site); `/design (primitives)` (would adjust `extern_shims()` visibility if the consuming site needs it).

**Evidence available from primitives-narrow audit.**
- `extern_shims()` is private to `cranelisp-primitives::lib.rs` (no `pub` modifier).
- The macros-module construction site is NOT in `cranelisp-primitives` (no `cranelisp-frontend` or `cranelisp-int` reference inside the crate).
- The `sconcat` fn-ptr must reach the `macros` module's GOT somehow at session init.

**Possible mechanisms (audit cannot pick from primitives-narrow viewpoint).**
1. The macros-module construction site has its own duplicate harvest of `marshal::sconcat` via a different visible path (e.g., the `pub mod marshal` line plus a `pub(crate)`-or-higher `sconcat` re-export). Requires inspection of the macros construction site to confirm.
2. The macros-module construction site lives in `cranelisp-primitives` itself (sibling of `PRIMITIVES_TABLE`) and consumes `extern_shims()` internally. Not visible in `lib.rs` today — would require source addition.
3. The `sconcat` fn-ptr is reached via a different mechanism altogether (linker-name resolution at JIT-builder time, registered separately by frontend/int). Possible if `JITBuilder::symbol("sconcat", marshal::sconcat as *const u8)` is called somewhere outside primitives.

**What tips the choice.** Inspection of the macros-module construction site (`/design (frontend)` or `/design (int)` narrow audit). The audit cannot do this from primitives-only deployment.

**Concrete next step.** Surface to the next frontend or int audit (S69 Wave 1 or W2). If the construction site duplicates the harvest, the duplication is a finding in *that* audit (not primitives'); resolution may lift `extern_shims()` to `pub` or `pub(crate)`-with-`#[cfg(test)]`-exposure. If the construction site has a clean alternate mechanism, no primitives-side change is needed.

**Note.** This is **not blocking F2**. F2's facade-moves can land in S69 W2 (split the §"Marshalling" subsection so `sconcat` is named correctly per spec) without resolving A2. A2 is the source-side cleanup path *if* duplication is found downstream.

---

## 5. Verdict

**SMALL DRIFT** in count (11 findings: 3 facade-moves, 1 source-moves, 4 no-action confirmations, 2 coverage notes, 1 no-action revised). **Substantial in re-grounded rationale at F1 and F4 and F11.**

- **F1 (Cargo↔facade contradiction on intrinsics dep)** — facade-moves, same direction as prior, but grounded against Decision 0043 §"Migration scope" + Decision 0048 §"Structural invariant" + Principle 8 rather than the prior version's Principle-15 misapplication. The contradiction has been latent for one sprint; closing it removes ambiguity for the workspace-DAG reader.

- **F4 (FIXME 0212 `#[used]` binary)** — **disposition flipped from facade-moves to source-moves**. Decision 0048 §"Consequences" explicitly names `#[used]` as the canonical mechanism; the prior audit's recommendation to retire `#[used]` on Principle 7+18 grounds would have overridden the binding Decision text without filing a Decision-amendment FIXME first — the regression-mechanism risk the audit-discipline default explicitly prohibits. F4 closes in S69 via 45 single-line `#[used]` additions; Option 2 routes through optional follow-on A1 if pursued on its independent architectural merit.

- **F11 (dep-ban test symmetry)** — recommendation flipped from "optional symmetric test" to "no symmetric test (Principle 18 covers structurally)". The forward edge failure mode surfaces at compile time as a Rust error; no dedicated test surface earns its keep.

- **F2 (sconcat placement)** — disposition simplified from both-move to facade-moves; the source-side visibility question routes to downstream cross-crate audit (arbitration A2) rather than committing primitives-side to a visibility change.

- The remaining findings (F3, F5, F6, F7, F8, F9, F10) are unchanged in disposition; F3's facade-prescriptive revision and the four alignment confirmations + two coverage notes are routine.

**Wave 3 source work in S69**: F4 only — 45 `#[used]` attributes across `crates/cranelisp-primitives/src/{ring0,bool,int,float,marshal,string,vec}.rs`. `/dev (primitives)` delivery. All other resolutions are doc-only Wave 2 facade revisions.

**The audit cannot resolve alone (genuinely unsourced)**:
- **A1** (Decision 0048 §"Consequences" `#[used]` retire) — optional follow-on if Principle 7+18 weight is judged sufficient on independent grounds. `/arch` authority.
- **A2** (`sconcat` cross-module wiring visibility) — downstream cross-crate audit (`/design (frontend)` or `/design (int)`). Not blocking F2.

**Total finding count**: 11 (F1–F11). **Prior dispositions flipped: 3 (F2, F4, F11).** **Rationale rewritten: 1 (F1).** **Most consequential flip: F4** — respecting Decision 0048's binding `#[used]` text on the audit-discipline default rather than overriding it on Principle-grounds.

---

## Cross-references

- `design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md` — binding source for the post-S68 shape (esp §"Shape", §"Consequences", §"Structural invariant — backend dep-ban")
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — binding source for allocator placement (F1 grounding)
- `design/arch/decisions/0035-code-enum-integration-layer.md` — GOT is single source of truth (F10 grounding)
- `design/arch/facades/primitives.md` — facade under audit
- `design/arch/principles/07-single-source-of-truth.md`, `08-no-interim-implementations.md`, `15-facade-types-live-with-behavior.md`, `18-enforce-invariants-structurally.md`
- `design/arch/bounded-contexts.md` §4a — Primitives BC
- `design/arch/CLAUDE.md` §"Baseline-diff discipline" — F3 grounding
- `crates/cranelisp-primitives/src/lib.rs` — declared surface (incl in-crate tests at lib.rs:263–414)
- `crates/cranelisp-primitives/public-api.txt` — live boundary
- `crates/cranelisp-primitives/Cargo.toml` — dep invariants (F1)
- `crates/cranelisp-backend/tests/no_primitives_dep.rs` — workspace dep-ban test (F11)
- `design/arch/fixmes/0212-primitives-used-attribute-discipline.md` — `#[used]` contract gap (F4); closes on F4 source-moves landing
- `design/arch/fixmes/0210-arch-primitives-as-uniform-module-with-symboltable-and-got.md` — the primary FIXME Decision 0048 resolves
- `spec/09-macros.md` §9.7.3 — `sconcat` placement (F2 grounding)
- `spec/appendix-a-builtins.md` §A.3 — `not` primitive spec (F6 grounding)
- `~/.claude/projects/.../memory/feedback_audit_per_item_analysis.md` — discipline that grounds this re-author
- `sprints/SPRINT.md` §"Architecture review (Phase 2)" — Wave 1 audit briefs (the watch items this audit responds to)
