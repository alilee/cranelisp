# D1 — Introspection is REPL-only; macro `sexp` returns to the symbol table

**Status:** RULING (S80 Wave 2D, `/arch`, 2026-06-13). User-ratified architectural
direction; persisted at `memory/introspection-repl-only-principle.md`.

**Scope:** a cross-crate data-model ruling. It reverses **Decision 41's** placement
of macro `sexp` (one field, for the compile path only), re-homes introspection
population to REPL mode, and names the explicit mode carrier that replaces the
`introspection.is_some()` proxy. This document is the manifestation site for the
*types-crate* change and the *cross-surface* (int) consequences; the per-site `/dev`
implementation scope is enumerated in §6. The `crates/cranelisp-types` change is
landed by this ruling (the `macro_sexp` field on `DefKind::Macro` + public-api
baseline); all `src/` changes are `/dev` int's.

---

## 1. Decision 41's original rationale — and why this reversal does not reintroduce it

**What D41 did.** Decision 41 (and the S69/S70 settlement of the `DefKind::Macro`
variant) deliberately **retired the per-entry `sexp`/`source` fields** and moved that
data to the integration-layer `Introspection` record (`SharedState.introspection:
DashMap<FQSymbol, Introspection>`, `src/session_v4.rs`). The rationale, verbatim from
the `DefKind::Macro` rustdoc as it stood pre-D1:

> *Macros are not architecturally special for introspection purposes … carrying
> `sexp`/`source` on `DefKind::Macro` would duplicate the canonical store
> asymmetrically (no other `DefKind` variant carries them — `UserFn`,
> `Constructor`, etc. all rely on the integration-layer `Introspection` map).*

So D41's concern was **symmetry**, not serialization. The driving worry was that
`source`/`sexp`/`expanded`/`clif_ir`/`disasm`/`code_size` are a uniform *REPL-display*
concern across **all** Def kinds, and the right home for that uniform concern is one
per-`FQSymbol` record in the int layer — not a scatter of per-variant fields. D41 was
NOT motivated by a cache-roundtrip / `#[serde(skip)]` problem: `DefKind::Macro` already
serializes its `clauses_meta` into the disk cache with no trouble, and `Sexp` already
derives `Serialize`/`Deserialize`. (The "cache-hit residual gap" the rustdoc noted is
the *opposite* problem — that `Introspection` is **non**-serialized and so is absent on
cache restore.)

**Why the reversal is sound.** The S80 user ruling exposes the real defect: a
**compile-path read** (`worker::resolve_macro_sexp_from`, used by on-demand macro-clause
recompile during FQ-autoload and cache-restore) was sourced from `introspection`. To
satisfy that read in non-REPL modes, S78 made `cluster::process_cluster` populate
`introspection: Some(&shared.introspection)` **unconditionally** — which broke the
REPL-vs-batch discriminator that `worker.rs:2851` derived from `introspection.is_some()`.
The fix is not to make introspection always-on; it is to **move the one piece of
compile-necessary data onto the symbol table** ("it's in the name" — introspection is a
REPL facility).

The reversal is **narrow and does not undo D41's symmetry**:

- It re-homes **only** `sexp`, and **only on `DefKind::Macro`** — the one kind whose
  *compile* path needs the original form. It does **not** reintroduce a generic
  `Def.sexp`/`Def.source`.
- Every *other* Def kind stays exactly as D41 left it: `source`/`expanded`/`clif_ir`/
  `code_size` (and the `/sexp` *display*) remain on the int `Introspection`
  record for REPL display. D41's symmetry holds for the introspection readers. (The
  `disasm` field that D41 also enumerated here is dropped — S87 Wave 0, FIXME 0418
  option (a): native disassembly is on-demand via `cranelisp_backend::produce_disasm`,
  not a persisted-introspection field; see §"Reader handling".)
- Macros are uniquely justified: they are the **only** Def kind with **no
  `ast: Option<DefnVariant>`** to carry a compile payload (a macro parent's clause
  bodies are separate mangled-name Defs; the parent entry has no `ast`). So the recompile
  source has *nowhere else* to live on the entry. Every other kind carries its compile
  input as `ast`; macros need `macro_sexp` for the identical reason.

**What D41 solved stays solved**, because the residual it actually guards against
(serializing the whole `Introspection` record into the cache — mixing REPL concerns,
bloating the cache, raising invalidation questions) is **not** what this ruling does.
`macro_sexp` is a single parsed form, the macro's own definition, the minimal
compile-necessary payload.

---

## 2. Where macro `sexp` lives now — the symbol-table shape

The macro source form is carried on the macro parent entry's kind:

```rust
// crates/cranelisp-types/src/module.rs — DefKind
Macro {
    clauses_meta: Vec<MacroClauseInfo>,
    /// The macro's original `(defmacro name …)` form. Compile-path data:
    /// the recompile path (resolve_macro_sexp_from → parse_defmacro →
    /// compile_macro_with_state) reads it to rebuild clause code when the
    /// GOT slot is empty (FQ-autoload of a cross-module macro; cache-restore
    /// where the clause `.o` was not linked inline).
    macro_sexp: Sexp,
}
```

**Serde / cache strategy.** `macro_sexp` is **serialized** (no `#[serde(skip)]`),
exactly like its sibling `clauses_meta`. This is the load-bearing property:

- **Cache-restore — the harder of the two readers — is solved by serialization, with no
  rehydration step.** A cache-restored macro entry carries its `macro_sexp` directly off
  the deserialized symbol table. The recompile path reads the entry; it does not consult
  `introspection` (which is non-Serde and absent on cache restore — the very reason the
  old `resolve_macro_sexp_from` returned `None` for cache-restored modules, forcing the
  S77 `handle_cached_codegen` work-around at `worker.rs:621` Step 2a).
- **FQ-autoload** populates the entry through the normal register path
  (`register_macro_in_module`, §6), so the field is present in-memory before the
  recompile path runs.

`Sexp` derives `Serialize`/`Deserialize` and is already a cross-crate `cranelisp-types`
type, so the field adds no new serialization machinery. The serialized cost is one parsed
form per macro Def, bounded by source size — acceptable for compile-necessary data.

**Type-crate change (landed by this ruling):**

- `crates/cranelisp-types/src/module.rs` — `DefKind::Macro` gains `macro_sexp: Sexp`;
  the variant rustdoc rewritten to state the D1 introspection-vs-compile split.
- `crates/cranelisp-types/src/resolve.rs` — the `macro_kind()` unit-test helper supplies
  a placeholder `macro_sexp: Sexp::List(vec![], Span::SYNTHETIC)`.
- `crates/cranelisp-types/public-api.txt` — regenerated; **one additive line**
  (`pub cranelisp_types::DefKind::Macro::macro_sexp: cranelisp_types::Sexp`).
  `cargo check -p cranelisp-types` clean.

---

## 3. Introspection reverts to REPL-only population

`introspection` is a REPL slash-command facility (`/sig`, `/doc`, `/source`, `/sexp`,
`/clif`, `/disasm`). It MUST be populated **only in REPL mode**. The compile pipeline
reads nothing from it.

**The gating change.** `cluster::process_cluster` (`src/cluster.rs:222`) currently
constructs the `ModuleCompiler` with `introspection: Some(&shared.introspection)`
unconditionally. This becomes **conditional on REPL mode**:

```rust
introspection: if shared.run_mode.populates_introspection() {
    Some(&shared.introspection)
} else {
    None
},
```

i.e. `Some(..)` only when the session's run mode is `Repl` (see §4). `--run`/`--link`
pass `None`.

**Remaining writes — confirmed correct, no change needed beyond the gate above:**

- `worker.rs:1759` (regular-defn introspection population) and `worker.rs:2171`
  (`/source` source-text capture) are already `if let Some(intr_map) = ctx.introspection`
  / `if ctx.introspection.is_some()` guarded, commented `--repl only`. With the
  `cluster.rs:222` gate now feeding `None` in batch, these become no-ops in `--run`/`--link`
  automatically — which is the intended behavior.
- `register_macro_in_module` (`worker.rs:1547`) still writes macro `sexp`/`source` into
  `introspection` for REPL display — but it MUST also write `macro_sexp` into the
  symbol-table entry it builds (§6), unconditionally, because that field is the
  compile-path source.

**REPL-command reads — confirmed correct, unchanged:**

- `session_v4.rs` `symbol_source` / `symbol_sexp` / `symbol_clif` (and the `/disasm`,
  `/expand` reads) continue to read from `introspection`. In REPL mode the map is
  populated as before. These are REPL-only by construction.
- `save::generate_module_source` (`src/save.rs`, REPL persist / `regenerate_backing_file`)
  reads the macro sexp via `introspection_sexp`. **It still has its data in REPL mode**
  (that is the only mode that persists `.cl` files). **Recommended hardening (§6):** have
  `generate_module_source`'s macro branch fall back to the symbol-table `DefKind::Macro
  .macro_sexp` when the introspection record is absent — this closes the cache-restored-
  then-REPL-edited macro-drop gap (the FIXME-0299 root #2 symptom) for free, since the
  field now round-trips the cache. This is an int decision; the data is available either
  way.

---

## 4. The mode signal — explicit run-mode carrier on `SharedState`

**Problem.** There is no run-mode field on `Settings`/`SharedState` today. `main.rs`
knows `Action::{Run, Repl, Link}` but never threads it; the hash-gate and the
introspection-population decision both inferred mode from `introspection.is_some()`,
which is exactly the conflation the user rejected.

**Carrier.** Introduce an explicit **`RunMode`** enum, set from `main.rs`'s `Action`,
carried on `SharedState` (int-internal session state):

```rust
// src/session_v4.rs (int — NOT cranelisp-types)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunMode {
    /// `cranelisp` with no/REPL target — interactive prompt; populates
    /// introspection; layout-hash drift WARNS-AND-LOADS.
    Repl,
    /// `cranelisp --run <file>` — batch execute then `process::exit`;
    /// no introspection; layout-hash drift REFUSES.
    Run,
    /// `cranelisp --link <file>` — produce a standalone executable;
    /// no introspection; layout-hash drift REFUSES.
    Link,
}

impl RunMode {
    /// Introspection is REPL-only.
    pub fn populates_introspection(self) -> bool { matches!(self, RunMode::Repl) }
    /// The layout-hash gate's `is_repl` discriminator (REPL warns; Run/Link refuse).
    pub fn is_repl(self) -> bool { matches!(self, RunMode::Repl) }
}
```

**Why int-internal, not `cranelisp-types`.** `RunMode` is a property of the running
session — which CLI verb launched it. It crosses no crate boundary (frontend / typecheck
/ backend never see it; backend's codegen-strategy axis is the *separate*
`CompileMode::{Interactive, Batch, Release}` in `interfaces.md` §"CompileMode", which is
orthogonal — it governs GOT-indirect-vs-direct codegen, not REPL-vs-batch session
behavior). Per Principle 15 (facade types live with behavior) and the BC §6 placement of
session orchestration in int, `RunMode` lives in `src/session_v4.rs` beside
`SharedState`. **Do not conflate it with `CompileMode`** and **do not add it to
`cranelisp-types`.**

**Plumbing.** `main.rs` constructs the session with the `Action`-derived `RunMode`
(threaded through `CompilerSession::new` / `Settings`, an int-side wiring choice). The two
readers switch source:

- `worker.rs:2851` — `let is_repl = ctx.run_mode.is_repl();` (replacing
  `ctx.introspection.is_some()`). `ModuleCompiler` carries `run_mode: RunMode` (or reads
  it via `ctx.shared_state`); `layout_hash_gate(dll_hash, &host_hash, name, is_repl, span)`
  is **unchanged** — only its `is_repl` *argument source* changes. Its logic and unit
  tests (which pass `is_repl` explicitly) stay correct.
- `cluster.rs:222` — the introspection gate (§3) reads
  `shared.run_mode.populates_introspection()`.

This makes the **downstream symptom** disappear: `--run` (`RunMode::Run`) yields
`is_repl == false`, so a drifted platform layout-hash **REFUSES** (exit non-zero) instead
of warns-and-loads — `hash_gate_run_refuses` goes green.

---

## 5. Public-API impact

- **`cranelisp-types` changed.** `DefKind::Macro` gains `macro_sexp: Sexp`.
- **Baseline regen — REQUIRED and DONE.** `crates/cranelisp-types/public-api.txt`
  regenerated via the canonical command
  (`cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-types`).
  The diff is a single additive line; committed alongside this ruling. The
  `DefKind` enum is not `#[non_exhaustive]` at the variant-field level, so the new field
  is a source-visible addition — the baseline diff is the audit record.
- **`RunMode` is int-internal** — it appears in `crates/cranelisp` (the binary) public
  surface only insofar as int exposes it; that baseline (if any) is `/dev` int's to
  regenerate when it lands the field. No `cranelisp-types` consequence.

---

## 6. Implementation scope for `/dev` int (precise sites)

All `src/` work. `crates/cranelisp-types` is already landed by this ruling.

| Site | Change |
|---|---|
| `src/session_v4.rs` (~`RunMode`, `SharedState`) | Add `RunMode` enum (§4) + `run_mode: RunMode` field on `SharedState`. |
| `src/main.rs` `Action` → session ctor | Derive `RunMode` from `Action::{Run, Repl, Link}`; thread into `CompilerSession::new` / `Settings` → `SharedState.run_mode`. The only legitimate place `Action` becomes `RunMode`. |
| `src/cluster.rs:222` (`process_cluster`) | Gate `introspection:` field — `Some(&shared.introspection)` only when `shared.run_mode.populates_introspection()`, else `None`. (Removes the unconditional `Some`.) |
| `src/worker.rs:2851` (platform hash gate) | Replace `let is_repl = ctx.introspection.is_some();` with `let is_repl = ctx.run_mode.is_repl();` (thread `run_mode` onto `ModuleCompiler`, or read via `ctx.shared_state`). `layout_hash_gate` call unchanged. |
| `src/worker.rs:1547` `register_macro_in_module` | When building the `DefKind::Macro { clauses_meta }` entry, also set `macro_sexp: sexp.clone()` (the `sexp: &Sexp` arg is already in hand). This is **unconditional** (compile-path data). The existing `introspection`-write block (REPL `sexp`/`source` for display) stays, now no-op in batch via the §3 gate. |
| `src/worker.rs:736` `resolve_macro_sexp_from` | Re-source from the **symbol table** instead of `introspection`: read the `DefKind::Macro .macro_sexp` off the entry for `(defining_module, name)` (via `read_macro_meta`-style lookup or a sibling accessor), returning `Some(sexp.clone())`. Drop the `shared.introspection.get(&fq)` read. This now works for **cache-restored** modules (the field round-trips), so the same-vs-cross-module guard at the call site (`worker.rs:675`) and the `handle_cached_codegen` Step 2a drive (`worker.rs:621`) remain correct but the introspection-absence failure mode is gone. |
| `src/worker.rs:621` Step 2a + `:675` caller | No structural change required, but re-verify: with `macro_sexp` now available on cache-restored entries, the Step-3 recompile fallback (`resolve_macro_sexp_from`) can succeed where it previously returned `None`. Keep the cross-module guard (the §0.2 forward-reference rejection) intact. |
| `src/save.rs` `generate_module_source` / `introspection_sexp` | **Recommended:** macro branch falls back to symbol-table `DefKind::Macro .macro_sexp` when the introspection record is absent (closes the cache-restored-then-REPL-edited `defmacro`-drop gap for free). REPL data path otherwise unchanged. |

**Verification anchors.** `tests/…::hash_gate_run_refuses` goes green (the D1 red).
The existing `layout_hash_gate` unit tests stay green (logic unchanged). Macro
round-trip tests that exercised the `resolve_macro_sexp_from` path
(`mode_equiv_macro_user_defined` family, persist-restart macro tests) must stay green
against the symbol-table source.

**Out of scope for this ruling:** D2 (`--link` layout-hash NUL-termination,
`/dev` backend/int) and D3 (`/qa` test fix) are separate Wave-2D items.

---

## 7. Canonical-set audit (this ruling's sweep)

- **`crates/cranelisp-types/src/module.rs`** — `DefKind::Macro` rustdoc rewritten:
  the "Why no `sexp`/`source` field here" block is replaced by the **introspection-vs-
  compile split**; the "cache-hit residual gap" note is re-scoped (compile path no longer
  blocked; only the REPL-introspection reader retains the lazy-reread future fix).
- **`crates/cranelisp-types/public-api.txt`** — regenerated (one additive line).
- **`design/arch/bounded-contexts.md` §6 (int)** — the "Development tooling: …
  introspection" bullet gains the D1 qualifier: introspection is **REPL-mode-only**
  (populated only under `RunMode::Repl`); compile-necessary data lives on the symbol
  table; the run-mode signal is the explicit `RunMode` carrier on `SharedState`, not
  `introspection.is_some()`.
- **`design/arch/interfaces.md`** — the `CompileMode` note gains a one-line disambiguation
  that `RunMode` (REPL/Run/Link, int-internal) is a **separate** axis from `CompileMode`
  (codegen strategy).
- **Decision 41 file** (`design/arch/decisions/0041-*.md`) — annotated with a D1
  reversal pointer (drain backlog; the substance lives here + BC §3/§6 + the source
  rustdoc).
- **Principles** — no new principle. The ruling is a direct application of Principle 7
  (single source of truth — compile data has one home, the symbol table), Principle 1
  (decoupling — REPL facility is not a compile dependency), and Principle 19 spirit
  (no facility privileged into a role it does not own). Confirmed; no edit.

---

# D1b — The introspection STORE must not exist outside REPL

**Status:** RULING (S80 Wave 2D, `/arch`, 2026-06-13). User-ratified architectural
direction; persisted at `memory/introspection-repl-only-principle.md` (the "Fuller
structural target" paragraph). **D1b EXTENDS D1.** D1 moved the one compile-necessary
datum (macro `sexp`) onto the symbol table and gated introspection *population* on
`RunMode`. D1b finishes the job at the **structure** level: the introspection store is
made `Option<DashMap>`, **`None` outside REPL**, so in batch the store does not merely go
unpopulated — it does not *exist*, and the introspection-only codegen byproducts (CLIF-IR
text) are not generated at all.

**Scope:** int-internal only. `SharedState.introspection` and the int-internal
`Introspection` record (`src/session_v4.rs:627`) are entirely below the crate boundary.
**No `cranelisp-types` change. No public-API / baseline change.** (Confirmed in §B5.)

---

## B1. MANDATORY history finding — was REPL-only intended, or always-present deliberate?

The user required, before any reversal, a broad review of the decisions log + design docs
(including legacy/archive) to establish whether REPL-only introspection was the
**intended-but-undocumented** shape that drifted, or whether always-present introspection
was a **deliberate reversal with a rationale to preserve** — exactly how D1 found
Decision 41 was deliberate-for-symmetry and had to be designed around rather than blindly
reverted.

**Finding: REPL-only was the intended shape from day one. The always-allocated `DashMap`
was incidental scaffolding, never a deliberate "must be live in batch" reversal. The
`Option` change is safe.**

Evidence:

1. **Origin commit.** `introspection` entered the codebase in `0bc433f` ("session
   restructure Phase A+B: target types"), authored as a plain `dashmap::DashMap` sibling
   of `typecheck_products`, `codegen_inputs`, `codegen_products` — all four scaffolded as
   bare always-allocated DashMaps in one stroke. Its doc-comment **at birth** read:
   *"REPL-only per-symbol introspection data. **Not populated during batch.**"* The
   REPL-only *intent* is the original design statement; the always-present *allocation*
   was simply the uniform shape the four target-model maps were stamped out in. There is
   no commit, decision, or design note that ever argued introspection must be live in
   batch.

2. **Never an `Option`.** `git log -S 'introspection: Option' -- src/session_v4.rs`
   returns empty across the whole history — the field has *always* been a plain `DashMap`;
   the `Option` form has never existed and was never rejected. So there is no prior
   `Option`→`DashMap` reversal to reconcile (contrast D1's Decision 41, which *was* a
   deliberate field-removal with a recorded symmetry rationale).

3. **The design-level home agrees.** The `TypecheckProduct.source_text` rustdoc
   (`session_v4.rs:613`) and the `Introspection` rustdoc (`:624`) both already say
   "retained in `--repl` mode … None for cache-hit modules and batch mode" — the
   *design* always treated introspection as a REPL facility; the always-present container
   was an implementation accident, not a design commitment.

4. **The drift that made it look load-bearing was S78, and D1 already corrected the
   read.** The S78 single-orchestration unification made `cluster::process_cluster`
   populate `introspection: Some(...)` unconditionally to satisfy one *compile-path read*
   (`resolve_macro_sexp_from`). That was the layering violation D1 fixed by moving
   `macro_sexp` to the symbol table. **Post-D1, no compile-path reads introspection** (§B3
   re-confirms). So nothing depends on it being live in batch.

**No still-valid reason for batch-liveness was found.** I therefore rule FOR the
`Option<DashMap>` reversal. (Per the user's instruction to say so if the review found a
reason to keep it live: there is none — the recommendation is to proceed.)

### B2. Does any NON-REPL path read `shared.introspection`? — re-confirmed: no

D1's `/review` established no compile-path read survives post-D1. D1b re-confirms across
the broader batch consumers the user named (test discovery, trace, `--link` artifact
routing, save/persist):

- **Compile path:** `resolve_macro_sexp_from` now reads `DefKind::Macro.macro_sexp` off the
  symbol table (D1 §6), not introspection. No other `process_cluster` /
  `inline_jit_codegen_*` / macro-expansion site reads it.
- **Test discovery** (`discover_tests_extern`, `run_test_by_name`): reads the live symbol
  tables + `TestRunnerState`, never `introspection`.
- **Trace** (`cranelisp_trace_*`, `trace_format`): self-contained codegen-baked
  `DisplayDescriptor`s in the intrinsics/backend (see `tracing.md`) — no int introspection
  involvement.
- **`--link` artifact routing** (exe-bundle, GOT/manifest/schema): reads symbol tables +
  the platform manifest, never introspection.
- **Save / persist** (`save::generate_module_source`, `regenerate_backing_file`,
  `session_v4.rs:1914`): a REPL-only path (only the REPL persists `.cl` backing files).
  It reads introspection for verbatim REPL input text, with a symbol-table
  `macro_sexp` fallback already specified in D1 §6 — so it functions when a record is
  absent, and it never runs in `--run`/`--link` anyway.

**Every reader of `shared.introspection` is REPL-mode-reachable only.** Making the store
`None` in batch removes nothing any batch path consumes.

---

## B3. The `SharedState.introspection: Option<DashMap>` ruling

`SharedState.introspection` changes from
`dashmap::DashMap<FQSymbol, Introspection>` to
`Option<dashmap::DashMap<FQSymbol, Introspection>>`:

```rust
// src/session_v4.rs — SharedState
/// Per-symbol introspection data, **REPL-only** (D1/D1b). `Some(map)` only
/// under `RunMode::Repl`; `None` in `--run`/`--link` — the store does not
/// exist in batch (it is not merely unpopulated). The compile pipeline reads
/// nothing from it (macro `sexp`, the one compile datum, lives on the symbol
/// table per D1). Slash commands (`/sig`,`/doc`,`/source`,`/sexp`,`/clif`,
/// `/disasm`) read it; absent ⇒ they no-op.
pub introspection: Option<dashmap::DashMap<FQSymbol, Introspection>>,
```

**Construction** (`session_v4.rs:1201`, `CompilerSession::new`): the field is built from
the same `run_mode` already threaded into the ctor (D1 §4) —
`introspection: run_mode.populates_introspection().then(dashmap::DashMap::new)`. `Repl`
⇒ `Some(empty map)`; `Run`/`Link` ⇒ `None`. No allocation occurs in batch.

**Why `run_mode.populates_introspection()` is the single source of the `Option`.** The
`Some`/`None` discriminator is exactly the REPL-vs-batch signal D1 already established. The
store's existence and its population are now driven by the **same** carrier — there is no
second discriminator to drift. This is the structural completion of D1's population gate:
D1 made the *writes* conditional on `populates_introspection()`; D1b makes the *container*
conditional on the same predicate, so the conditional-write sites become trivially correct
(no map to write into).

### Reader handling (`None` ⇒ no-op, by construction)

The four REPL-command read accessors and the two ad-hoc readers switch from
`self.shared.introspection.get(fq)` to `self.shared.introspection.as_ref().and_then(|m|
m.get(fq))` — yielding `None` when the store is absent. They are **REPL-only by call
path** (slash-command handlers only fire in the interactive loop), so in practice the
store is always `Some` when they run; the `.as_ref()` is a compile-time necessity, not a
behaviour change. Sites:

| Reader | Site | `None` behaviour |
|---|---|---|
| `symbol_source` / `symbol_sexp` / `symbol_clif` | `session_v4.rs:1524/1531/1539` | already return `Option`; `None` flows out as "no record" — the exact documented batch semantics ("`None` … in production batch mode"). |

> **`symbol_disasm` / `Introspection.disasm` removed (S87 Wave 0; FIXME 0418 option (a)).**
> The read-side accessor family no longer includes a disasm accessor. Native
> disassembly is **on-demand**, re-derived per request via
> `cranelisp_backend::produce_disasm(fq, code_size, symbol_tables)` (Decision 41 —
> "Disassembly is NOT captured … `produce_disasm` re-derives it on demand"; §B4 above).
> The former `Introspection.disasm: Option<String>` field was never written (the worker
> asserted it stayed `None`) and was read only by `symbol_disasm`, which had no correct
> caller once `/disasm` moved to the on-demand path; both the field and the accessor are
> dropped. Unlike `source`/`sexp`/`clif_ir`, disasm is not a persisted-introspection
> accessor — it is a derive-on-demand product, so it leaves the accessor family entirely
> rather than being rehydrated lazily like the others.
| `describe_symbol` source read | `session_v4.rs:1627` | `source: None` in the returned `SymbolDescription` — correct. |
| `get_introspection` (`/source`,`/info`) | `session_v4.rs:2912` | returns `None` ⇒ handlers print "no source captured" — correct REPL fallback. |

`save::generate_module_source` (`save.rs:49`) currently takes `&DashMap`. Its single caller
is the REPL persist path (`session_v4.rs:1914`), where the store is always `Some`. Two
equivalent int-side options (the `/dev` call): pass `self.shared.introspection.as_ref()`
and have `generate_module_source` take `Option<&DashMap>` (each `introspection_sexp` read
becomes `Option`-aware, falling through to the D1 §6 `macro_sexp` symbol-table fallback);
**or** keep the `&DashMap` signature and have the caller pass an empty borrow when `None`.
The first is cleaner and dovetails with the D1 §6 fallback; recommended but `/dev`'s call.

### Drain handling

`cluster::insert_cluster` (`cluster.rs:283`) drains the cluster's
`introspection_records` into `shared.introspection.insert(...)`. This becomes
`if let Some(m) = shared.introspection.as_ref() { for (fq, intro) in … { m.insert(fq, intro); } }`.
In batch the cluster's `introspection_records` is already empty (the §3 population gate
fed `None` to the `ModuleCompiler`, so nothing was captured), so the drain is doubly a
no-op: nothing to drain, nowhere to drain it. Belt-and-braces consistent.

---

## B4. Codegen-product data-flow: retain-or-drop design

The user's data-flow ruling distinguishes two classes of codegen byproduct:

**Class 1 — free byproducts codegen knows anyway (`code_size`).** `code_size` is read
from the finalized `CompiledCode` (`backend lib.rs:1169`) — it is a near-zero-cost field
the codegen step already has in hand. **Ruling: it is generated unconditionally and
*returned to the worker*, which retains-in-REPL / drops-in-batch.** It already rides
`CompilationArtifacts.code_size` back to int; int's retention is the *write* into
introspection, which §B3 already gates. No backend change needed for `code_size`.

**Class 2 — data generated ONLY for introspection (CLIF-IR text, disasm strings).** These
must **not be generated at all in batch.**

- **CLIF-IR text.** `compile_one_function` (`backend lib.rs:1155`) computes
  `clif_ir = format!("{}", func.display())` **unconditionally** today and returns it on
  `CompilationArtifacts.clif_ir`. In batch this `String` is built, concatenated
  (`lib.rs:724/765`), returned across the crate boundary, and then **dropped unread**
  (int's step-7 write is gated, so nothing consumes it). This is the wasted work the user
  flagged. **Ruling: CLIF-IR text must not be generated when introspection is off.**
- **Disasm** is already correct — it is NOT captured in the always-created path
  (`lib.rs:1158` comment: "Disassembly is NOT captured … `produce_disasm` re-derives it on
  demand"); the `/disasm` REPL handler calls `produce_disasm` lazily. No batch disasm is
  generated. Confirmed; no change.

**The CLIF-IR generation sits in `cranelisp-backend`, not int — a boundary note.** The
unconditional `format!("{}", func.display())` is `/dev backend`'s code, below the int
boundary D1b is scoped to. Two dispositions, and the architectural ruling is explicit
about which:

1. **Preferred (full data-flow correctness):** `compile_to_module` gains a cheap
   `capture_clif: bool` flag (or a `CompileOptions` carrier) that int passes as
   `run_mode.populates_introspection()`. When `false`, `compile_one_function` skips the
   `func.display()` formatting and returns `clif_ir: String::new()`. This is a backend
   public-surface touch (one added bool parameter or an options field) → **a `/dev
   backend` change with a `cranelisp-backend` baseline regen**, filed as a FIXME `target:
   /backend` by `/dev int` when D1b lands, OR folded into the same wave if `/sprint`
   scopes backend in. It is the only part of D1b that crosses the int boundary.
2. **Acceptable interim (int-only, the D1b-in-int floor):** leave backend generating CLIF
   unconditionally; int's gated step-7 write (§B3) already drops it unread. The waste is
   one `String` format + one cross-boundary move per batch compile — bounded, not
   correctness-affecting. This is what the D1 `/review` Minor M1 already noted as
   "principle-residual, harmless."

**Ruling: the int-scoped D1b increment delivers disposition 2 (the store is `None`, all
int writes no-op, no record is allocated in batch — the user's primary structural target).
The CLIF-not-generated-in-batch refinement (disposition 1) is the *correct* end-state and
SHOULD be filed as a follow-up `target: /backend` FIXME**, because the generation site is
backend's and carries a baseline regen. Filing-not-implementing keeps D1b within its
int-only, no-public-API-change envelope while recording the remaining data-flow obligation
durably (per the project's defect-handoff discipline). `/sprint` may pull the backend
half into the same wave if it wants the complete data-flow correctness in one increment;
architecturally the two halves are independent and the int half stands alone.

### The two unconditional codegen-product sinks

The user named `worker.rs:3644`/`:4312` as the un-gated sinks. Re-mapped against current
source:

- **`worker.rs:4312`** (`handle_typecheck_work_shared` — the **pool-worker batch path**)
  passes `Some(&shared.introspection)` to `inline_jit_codegen_for_module`
  **unconditionally**. This is the real leak: in batch it feeds a live sink so step-7
  (`inline_jit_codegen_for_names:3771`, `intr_map.entry(fq).or_default()`) allocates an
  `Introspection` record per name and writes `clif_ir`/`code_size`. **Must become
  `shared.introspection.as_ref()`** — which yields `None` in batch (store absent), so
  step-7's `if let Some(intr_map) = introspection` short-circuits: no record allocated, no
  CLIF retained. (With `Option<DashMap>`, `.as_ref()` is exactly the right adaptor — it
  threads the store's existence straight through to the existing guard.)
- **`session_v4.rs:2524`** (the REPL eval codegen-and-finalize path) likewise passes
  `Some(&self.shared.introspection)` unconditionally. This path is REPL-reachable, but for
  uniformity and correctness it too becomes `self.shared.introspection.as_ref()` — `Some`
  in REPL, `None` if ever reached in batch. (The original `worker.rs:3644` line cited is
  the *parameter pass-through* inside `inline_jit_codegen_for_module`→`_for_names`; it
  carries whatever the caller supplied, so gating the two call sites above is sufficient —
  the pass-through needs no change.)

`inline_jit_codegen_*`'s sink parameter is **already `Option<&DashMap>`** (`worker.rs:451`,
`:3624`, `:3679`) and step-7 is **already `if let Some(intr_map) = introspection`-guarded**
(`:3765`). So no signature or guard change is needed in the codegen helpers — only the two
call sites stop hard-coding `Some(...)` and instead pass `…introspection.as_ref()`. The
`Option<DashMap>` store change makes `.as_ref()` the natural, single adaptor at every
producer site.

---

## B5. Public-API impact — none

- **No `cranelisp-types` change.** `Introspection`, `SharedState`, and `RunMode` are all
  int-internal (`src/session_v4.rs`), below the crate boundary. `Option<DashMap>` is a
  field-type change on an int struct.
- **No baseline regen for `cranelisp-types`.** Confirmed.
- **Backend (disposition-1 follow-up only).** IF the CLIF-not-in-batch refinement is taken,
  `compile_to_module` gains one parameter (or a `CompileOptions` field) → a
  `cranelisp-backend` baseline regen + BC §3 note, owned by `/dev backend`. That is the
  *follow-up* FIXME, NOT this int increment. The int-scoped D1b is public-API-neutral.

---

## B6. `/dev` int implementation scope (precise sites)

All `src/` (int). No `cranelisp-types` change.

| Site | Change |
|---|---|
| `src/session_v4.rs:885` (`SharedState.introspection` field) | Type → `Option<dashmap::DashMap<FQSymbol, Introspection>>`. Rustdoc → §B3 (store absent in batch, not merely unpopulated). |
| `src/session_v4.rs:1201` (`CompilerSession::new` ctor) | Build from the threaded `run_mode`: `introspection: run_mode.populates_introspection().then(dashmap::DashMap::new)`. No allocation in batch. |
| `src/session_v4.rs:2524` (REPL codegen-and-finalize producer) | `Some(&self.shared.introspection)` → `self.shared.introspection.as_ref()`. |
| `src/worker.rs:4312` (`handle_typecheck_work_shared` — pool-worker batch producer) | `Some(&shared.introspection)` → `shared.introspection.as_ref()`. **The core leak fix** — yields `None` in batch, so `inline_jit_codegen_for_names` step-7 (`:3765`) short-circuits: no record, no CLIF retained. |
| `src/cluster.rs:283` (`insert_cluster` drain) | Wrap the drain loop in `if let Some(m) = shared.introspection.as_ref() { … m.insert(fq, intro) … }`. (Doubly a no-op in batch — records empty AND store absent.) |
| `src/session_v4.rs:1524/1531/1539/1546` (reader accessors) | `self.shared.introspection.get(fq)` → `self.shared.introspection.as_ref().and_then(\|m\| m.get(fq))`. |
| `src/session_v4.rs:1627` (`describe_symbol` source read) | same `.as_ref().and_then(...)` adaptor. |
| `src/session_v4.rs:2336` (REPL eval source capture) | `self.shared.introspection.entry(fq)…` → `if let Some(m) = self.shared.introspection.as_ref() { m.entry(fq).or_default().source = … }`. REPL-only by path; compile-correctness under `Option`. |
| `src/session_v4.rs:2912` (`get_introspection`) | `.get(&fq)` → `.as_ref().and_then(\|m\| m.get(&fq))`. |
| `src/session_v4.rs:1916` + `src/save.rs:49/231–347` (`generate_module_source`) | Pass `self.shared.introspection.as_ref()`; make `generate_module_source` / `introspection_sexp` take `Option<&DashMap>`, falling through to the D1 §6 `DefKind::Macro.macro_sexp` symbol-table fallback when absent. (Or keep `&DashMap` + empty-borrow at the caller — `/dev`'s call; the `Option` form composes with the D1 §6 fallback and is preferred.) |
| `src/worker.rs:4524/4611` (`#[cfg(test)]`) | These build their OWN local `DashMap` for the unit test — **NOT** `shared.introspection`. No change. |

**Sites confirmed already-gated (no D1b change — verify only):** `cluster.rs:227`,
`session_v4.rs:2422`, `session_v4.rs:3494` already pass `Some(...)` conditionally on
`run_mode.populates_introspection()`. With the store now `Option`, these can stay as-is
(they pass `Some(&self.shared.introspection)` only in REPL, where the store is `Some` —
the inner `&DashMap` borrow is fine) OR be uniformly rewritten to `…introspection.as_ref()`
for one idiom everywhere. Recommend the latter for a single idiom; either is correct.

**Disposition-1 follow-up (NOT this increment):** `/dev int` files a FIXME `target:
/backend` — "`compile_to_module` should skip CLIF-IR `func.display()` formatting when
introspection is off (`capture_clif: bool` / `CompileOptions`); backend baseline regen +
BC §3 note." This records the Class-2 not-generated-in-batch obligation (§B4) durably.

**Verification anchors.** No new red is owed by D1b (it is a structural cleanup behind D1's
already-green behaviour): `hash_gate_run_refuses` stays green; the macro round-trip / cache
/ REPL-introspection tests stay green (the store is `Some` in every REPL test; `None` in
batch where nothing reads it). The D1 collateral guard `shared_state_field_count_at_target`
(FIXME 0324, 15→16) is unaffected by a field *type* change. A batch-mode assertion that
`shared.introspection.is_none()` under `RunMode::Run`/`Link` is the natural new positive
test (`/qa`, optional — the structural guarantee made observable).

---

## B7. Canonical-set audit (D1b sweep)

- **`design/arch/bounded-contexts.md` §6 (int)** — the D1 introspection qualifier extends:
  introspection is REPL-mode-only **and the store does not exist outside REPL**
  (`Option<DashMap>`, `None` in batch); codegen byproducts split into free-byproduct
  (`code_size`, returned + conditionally retained) vs introspection-only (CLIF-IR,
  not-generated-in-batch — the backend refinement filed as a follow-up). One-line addition
  to the existing D1 bullet; `/dev`/`/design` carry the source rustdoc.
- **`crates/cranelisp-types` / `interfaces.md`** — no change (int-internal).
- **`design/arch/bounded-contexts.md` §3 (backend)** — *if and when* the disposition-1
  follow-up lands, §3 gains a note that `compile_to_module` skips CLIF capture when
  introspection is off. Not now (the FIXME records it); flagged so the future backend
  change knows its manifestation site.
- **Principles** — confirmed, no new principle. D1b is the same Principle 7 / Principle 1 /
  Principle 19 application as D1, now at the storage-existence level: a REPL facility's
  *container* is not allocated where the facility is not offered. No edit.
- **Decision 41 file** — already annotated by D1; D1b adds nothing it must carry (D1b does
  not touch the macro-`sexp` half).
