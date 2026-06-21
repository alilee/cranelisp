# `cranelisp-platform` — Stage B deep audit (Sprint 87)

> **Delta + currency pass (2026-06-20).** Per `sprints/SPRINT.md` Stage B (R5
> same-instrument reconciliation). This is **not** a from-zero look — it opens by
> reconciling every finding in the named baseline `audits/platform-2026-06-14.md`
> (4 MED + 3 LOW), then walks the fixed 7-lens checklist (i)–(vii) with **heavy
> emphasis on lens (vii) — cross-crate / host-callback hygiene**, the class that
> bit S86 hardest. This crate **is** the host-callback boundary, so (vii) is the
> headline lens and carries its own section below.
>
> **Read-only on code.** No source/test/git state modified. Findings list
> *proposed* FIXMEs; this audit files none. Companion artefact:
> `audits/cranelisp-platform-s87-current-state.mmd` (fresh — the 06-14 baseline
> had no diagram).

**Module**: `crates/cranelisp-platform/src/` (4 files) + `tests/` (6 files)
**LOC (corrected, `audits/loc-s87.md`)**: 1,315 production + 583 external `tests/`.
Small but boundary-critical — the only crate with an external audience (DLL
authors) AND the single C-ABI seam between host and every platform DLL.
**Date**: 2026-06-20
**Scope**: 7-lens checklist; cross-crate/host-callback hygiene (vii); S86 seeds
(JIT-vs-`--link` host-callback divergence; FIXME 0407 characterization; fork-join
error-slot ferry visibility at the platform boundary).

---

## 1. Baseline reconciliation (`audits/platform-2026-06-14.md`)

The 06-14 baseline raised **4 MEDIUM + 3 LOW, no HIGH**. Six of seven are
**resolved**; one is **partially regressed** (a fresh one-bump staleness). Net:
the crate got *healthier* since the baseline — the macro was extracted, the R1
gate reframed, the unwraps hardened, and the latent grammar-drift risk got the
shared corpus the baseline asked for.

| Prior finding | 06-14 severity | S87 status | Evidence |
|---|---|---|---|
| **MED-1** `platform.md §3` two reworks stale (940-line single file, ABI v1, `jit_name` dispatch) | MED | **Resolved, with fresh residue → see F1** | `design/platform/platform.md:62` now reads "three files, 3,816 source lines, ABI v5, GOT-indirect, ADT marshaling"; `derive_jit_name`/`platform_fn_ptr`/`JITBuilder::symbol` deleted from live-surface sections (`:32`, `:84`). **BUT** the doc pins `ABI_VERSION = 5` (`:51`, `:88`, `:92`, `:99`, `:144`) while source is **6** (S86 DEF-5). One-bump stale, not two-rework stale. |
| **MED-2** R1 `null_alloc_with_tag` gate speaks as "not yet wired / FIXME 0229 / will be removed" | MED | **Resolved** | `lib.rs:475-497` rustdoc + panic message reframed to "permanent uninitialized-host fallback"; names no resolved FIXME, no removal promise. `t25` (`lib.rs:2255-2278`) updated to assert the reframed contract (no longer pins "FIXME 0229"). |
| **MED-3** schema grammar replicated across backend (generator) + platform (parser) with no shared corpus pinning agreement | MED | **Resolved** | `tests/platform_schema_roundtrip.rs` (new; cites "FIXME 0371 / MED-3") runs `cranelisp_backend::schema::generate_schema` → `cranelisp_platform::Schema::parse` on a representative corpus and asserts structural round-trip. The "drift escapes both suites + the layout-hash gate" hole is now closed by the one workspace test where both crates meet. |
| **MED-4** `lib.rs` 2,541 lines mixing 5 concerns; macro pair the extraction candidate | MED | **Resolved** | `declare_platform!` + `__declare_platform_body!` + `extract_layout_hash` extracted to `src/declare.rs` (409 lines). `lib.rs` is now the type/wrapper/const/HostContext surface; the three-exports emitter is findable by name in its own module. |
| **LOW-1** "owns no runtime state" inaccurate (3 process-globals) | LOW | **Resolved** | BC §5 (`bounded-contexts.md:378`) now reads "owns **no session-coordinated state**; its only state is three per-DLL write-once globals (`GLOBAL_ALLOC`, `GLOBAL_ALLOC_WITH_TAG`, `GLOBAL_SCHEMA`)". |
| **LOW-2** two guarded `.unwrap()`s in `schema.rs` parser | LOW | **Resolved** | `schema.rs:291` and `:469` are now `.expect("byte present — guarded by …")`. No production-path `.unwrap()` remains in `schema.rs`. |
| **LOW-3** hand-authored `CLAdtType` markers; stringly-typed `TYPE_NAME`, no generator | LOW | **Still open (deferred, as designed)** → see F5 | `adt.rs:55-77` rustdoc still says "the author writes the marker directly … or a future ergonomic layer generates them". Acceptable in the current zero-ADT-platform state; the `TYPE_NAME`-typo-→-runtime-panic gap persists. Tracked, not regressed. |

**Verdict on the baseline:** the 06-14 remediation plan was actioned almost in
full (MED-1/2/3/4 + LOW-1/2). The crate **still conforms to all nine BC §5
invariants and the three-exports model** and **still has no HIGH findings on the
interior lenses**. The one thing the baseline could not see — because it was an
interior-only pass — is the **cross-crate host-callback construction divergence**
(§3), which is where S86's DEF-6 actually lived.

---

## 2. Seven-lens checklist (i)–(vi); (vii) in §3

| Lens | Result |
|---|---|
| **(i) duplicated code paths / `mirror`** | One genuine duplication, cross-crate: the runtime `HostCallbacks` struct is hand-constructed at **two production sites** in two crates with no shared builder (§3, F2). Interior to the crate: the `CLIO::pure`/`effect_on_resource` node-build prologue (alloc → write header offsets → `payload - HEAP_HEADER_SIZE`) repeats the base-pointer dance 3× (`pure`, `effect_on_resource`, and each `CLString::from`), but each is short and the offsets differ — below the 3-identical-sites extraction bar. No `mirror` markers. |
| **(ii) dead paths** | None found. `null_alloc_with_tag` is **not** dead — it is the reframed permanent uninitialized-host fallback reached by in-crate construction tests (MED-2 resolution). No zero-call-site `pub fn` (the `produce_disasm` class) in this crate. |
| **(iii) function-budget overruns** | None. The largest fns are `manifest_to_descriptors` (~75 lines, `lib.rs:1360`) and `Schema::parse` (~58 lines, `schema.rs:242`) — both well under the ~100-line bar, both linear and single-concern. The macro arms in `declare.rs` are declarative, not a god function. |
| **(iv) RC-symmetry (Decision 24)** | Clean. `own()` (inc-on-wrap) vs `into_owned_consuming()` (take-caller's-transfer, no inc) — both dec on drop; the asymmetry is the documented consuming-capture protocol, pinned by 3 unit tests (`lib.rs:1659-1739`). `inc_rc`/`dec_rc` use `SeqCst` (matches Cranelift `atomic_rmw`; `Relaxed` rationale documented `lib.rs:1049-1061`). `CLAdt::construct` correctly uses `into_owned_consuming` (RC=1 from `alloc_with_tag`, no re-inc, `adt.rs:216-221`). |
| **(v) resolution-seam consolidation** | The manifest-symbol name has **one source of truth** — `platform_manifest_symbol()` (`lib.rs:246`), pinned to the macro's `concat!` by a unit test (`lib.rs:1766`). Good. The layout-hash data-symbol name is similarly single-sourced via the `concat!("__cranelisp_layout_hash_", name)` form. The one seam that is **not** consolidated is the host-callback construction itself (§3). |
| **(vi) interim-architecture residue (Principle 8)** | None active. The S71 schema-declaration DSL is fully retired across all four files (confirmed: no `jit_name`/`derive_jit_name`/`validate_schema`/`schema_literal`/`platform_fn_ptr` in source). The R1 gate was the last "temporary scaffold becomes permanent" smell and is now correctly reframed (MED-2). |

---

## 3. HEADLINE LENS (vii) — cross-crate / host-callback hygiene

This crate defines the C-ABI seam; the *wiring* of that seam lives in its
consumers. The S87 charter names the **JIT-vs-`--link` host-callback
divergence** (DEF-6 root enabler) as the thing to characterize. The verdict:

> **The divergence is real and structural, not a one-off bug.** DEF-6 was the
> *symptom*; the *root enabler* is that the runtime `HostCallbacks` value is
> hand-constructed independently at every host entry mode, with **no single
> shared builder**. The agreement between modes is maintained by manual mirroring
> and a code comment, not by construction. This is precisely the
> Principle-7 (single source of truth) / Principle-8 (mode divergence) pattern
> `memory/feedback_review_root_cause_and_duplication` warns about.

### 3.1 The divergence, concretely

There are **three** `HostCallbacks { … }` literal constructions that must wire
identical intrinsic fn-pointers, in three different modules across two crates
(plus this crate's tests):

| Site | Mode | `alloc` wired to | `alloc_with_tag` wired to |
|---|---|---|---|
| `src/platform.rs:253` | `--run` / REPL / JIT (`load_platform_dll`) | `cranelisp_intrinsics::heap_alloc_payload` | `…::alloc::cranelisp_alloc_with_tag` |
| `crates/cranelisp-exe-bundle/src/lib.rs:131` | `--link` startup stub (`cranelisp_init_platform`) | `…::alloc::heap_alloc_payload` | `…::alloc::cranelisp_alloc_with_tag` |
| `src/platform.rs:932` (`wired_host_callbacks`) | test helper "exactly as `load_platform_dll` does" | (mirror of site 1) | (mirror of site 1) |

The two *production* sites (1 and 2) are now **in agreement** — DEF-6 is fixed.
But the agreement is **by hand**: `cranelisp-exe-bundle/src/lib.rs:132-141` carries
a 10-line comment explaining that `alloc` MUST be `heap_alloc_payload` (not
`heap_alloc`) and that "the JIT path (`src/platform.rs`) already wires
`heap_alloc_payload`; **this makes the `--link` path match.**" That comment is the
tell: the contract is documented prose pointing at a sibling file, not a single
construction both modes call. DEF-6 was exactly the window where they *didn't*
match (one wired `heap_alloc` = base-returning; the other `heap_alloc_payload` =
payload-returning) — and nothing structural prevented it, because there is no one
place where "the host's callbacks" are defined.

### 3.2 Why the platform crate is implicated (and what it could offer)

The divergence does not live *in* `cranelisp-platform` — the crate correctly does
not depend on `cranelisp-intrinsics` (Principle 3; that edge would invert the
DAG). It cannot wire the callbacks itself. But it **owns the contract the wiring
must satisfy** and currently expresses that contract only as rustdoc on
`HostCallbacks::alloc` ("returns payload pointer (base + 16)", `lib.rs:446`) plus
the `def6_*` layout-invariant guards (`lib.rs:1946-2177`). The guards pin the
*platform-side half* of the invariant (a contract-honouring allocator lands the
stored base on the real allocation header) — they cannot pin that the *host*
wires a contract-honouring allocator in **every** mode, because the platform
crate never sees the host's wiring.

The structural fix is a consumer-side single source of truth (a shared
`HostCallbacks` builder in the lowest crate that can name both intrinsic pointers
— `cranelisp-intrinsics`, or a thin host-side helper both `src/platform.rs` and
`cranelisp-exe-bundle` call). That is an `/arch` + `/int` + `/backend` decision,
not a platform-crate edit — but it is the durable closure of the DEF-6 class and
belongs in the Stage B backlog. **F2** carries it.

### 3.3 The layout-hash export is the *good* counter-example

By contrast, the layout-hash export read path was built **mode-symmetric by
construction**: `declare.rs:202-208` documents that `--run` reads
`library.get::<*const &str>` → `**sym` and `--link`'s startup stub passes the same
symbol address to `cranelisp_check_layout_hash` which reads it as `*const &str` —
"the same `(ptr, len)` view, so the two modes read identically." This is the
shape the host-callback wiring *should* have: one data representation, both modes
dereference it the same way, no per-mode reconstruction. The contrast is
instructive — the layout-hash path is divergence-proof by representation; the
callback-wiring path is divergence-prone by hand-mirroring.

### 3.4 FIXME 0407 — same family, future task (CITED, not resolved)

Per the S87 charter, FIXME 0407 (Model-B closure-callback) is **cited as
host-callback-divergence evidence and stays open** — this audit does not action
it. It is the same family as the §3.1 divergence: 0407 wants to *widen*
`HostCallbacks` with `rc_inc`/`rc_dec`/`invoke_closure` (ABI v6→v7) so a platform
DLL can call back into a cranelisp closure (Model B `serve port handler`). When
that lands, it adds **three more fields** that every host-callback construction
site must wire identically — multiplying the §3.1 hazard by 3 across the same two
production sites. 0407's own "Proposed resolution" §2 already flags the three
sub-contracts (capture/RC, **error-slot ferry**, threading) that must hold
*across the FFI and across threads* — i.e. it is the closure-callback instance of
exactly the wiring-agreement problem DEF-6 was the allocator instance of. **The
F2 shared-builder fix is the natural prerequisite for landing 0407 safely**: do
not widen `HostCallbacks` until there is one place that constructs it. This is
the cross-cutting observation for the `/arch` synthesis.

### 3.5 Fork-join error-slot ferry — visible at this boundary?

The S86 fork-join error-slot ferry obligation (a worker-side panic swallowed —
the §12.4.3 defect) is **partially observable at the platform boundary, and the
platform half is sound.** The `EffectOutcome` mechanism (`lib.rs:688-727`,
`call_effect_thunk` `lib.rs:865`) is the platform-side ferry: a panic inside a
platform Effect thunk is caught **DLL-locally** (`effect_on_resource`'s
`catch_unwind`, `lib.rs:795-821`) and carried back across the C-ABI as a
`#[repr(C)] EffectOutcome` value rather than as a foreign unwind (which would
abort across the cdylib runtime boundary). This is the correct and only sound
design for the DLL→host direction, and it is well-tested
(`effect_thunk_panic_yields_fault_cause`, `lib.rs:1820`). **The gap the S86 seed
names is not here** — it is the *fork-join worker thread* swallowing the
`EffectOutcome`'s fault on the *joining* side (intrinsics/`src/worker.rs`
trampoline), where a faulted `EffectOutcome` ferried back from one Par branch must
propagate to the thread that joins the group. The platform crate hands the fault
back correctly as a value; whether the **intrinsics trampoline + fork-join join**
propagate that value (vs. drop it) is the open §12.4.3 obligation — out of this
crate's scope, flagged for the intrinsics pass / `/arch` synthesis. **F6** records
the boundary observation so the cross-crate trace is legible.

---

## 4. Findings (severity-ranked)

No HIGH. The host-callback divergence (F2) is **Important** because it is a
structural single-source-of-truth gap that has already produced one
heap-corrupting defect (DEF-6) and is the prerequisite for safely landing 0407 —
but it is *consumer-side* (not a platform-crate source edit), so it routes to
`/arch` for the synthesis, not to platform `/dev`.

### F1 — `platform.md` pins `ABI_VERSION = 5`; source is 6 (MED-1 residue)
**Severity**: Medium — design-doc currency → route to `/design`
**Files**: `design/platform/platform.md:51`, `:88`, `:92`, `:99`, `:144`; truth at `crates/cranelisp-platform/src/lib.rs:229` (`pub const ABI_VERSION: u32 = 6;`).
The 06-14 MED-1 rewrite refreshed §3 to the three-file/GOT-indirect shape but
landed at the then-current ABI v5; S86's DEF-5 (manifest export namespacing,
`cranelisp_platform_manifest_<name>`) bumped source to v6 and the doc was not
re-synced. The doc is now *one bump* stale (not two reworks), but a reader
trusting `platform.md §3.4`'s "v1→…→v5" bump-trail will under-count and miss the
v6 namespacing rationale — which is exactly the cross-platform-collision fix the
doc should explain. **Fix**: `/design` updates the five `ABI_VERSION = 5` /
"version 5" sites to 6 and extends the bump-trail with **v6** (S86 DEF-5 —
manifest export `_<name>` namespacing; `platform-interface.md` §5.5.5/§6.7). The
`ABI_VERSION` rustdoc (`lib.rs:184-228`) already carries the canonical v6 trail —
the doc should point at it rather than re-derive.
**Proposed FIXME**: `target: /design` — "Sync platform.md ABI v5→v6 + add the DEF-5 manifest-namespacing bump-trail entry."

### F2 — Runtime `HostCallbacks` is hand-constructed at two production sites with no shared builder (the DEF-6 root enabler; lens vii headline)
**Severity**: Important — cross-crate single-source-of-truth gap (Principle 7) / mode divergence (Principle 8) → route to `/arch` (synthesis)
**Files**: `src/platform.rs:253` (JIT/REPL), `crates/cranelisp-exe-bundle/src/lib.rs:131` (`--link`); contract owned at `crates/cranelisp-platform/src/lib.rs:444-473` (`HostCallbacks` + `alloc` rustdoc); `def6_*` guards `lib.rs:1946-2177`.
The two run-mode host entry points each construct `HostCallbacks { alloc, alloc_with_tag }` by hand. DEF-6 was the window where they disagreed (`heap_alloc` vs `heap_alloc_payload`); they now agree, but only by manual mirroring + a cross-file comment (`exe-bundle/src/lib.rs:132-141`: "this makes the `--link` path match"). Nothing structural prevents the next divergence — and 0407 (§3.4) will add three more fields each site must wire identically. **Fix** (`/arch` decision; `/int`+`/backend` implement): introduce one shared `HostCallbacks` builder in a crate that can name both intrinsic pointers (`cranelisp-intrinsics`, or a host-side `fn host_callbacks() -> HostCallbacks` both `src/platform.rs` and `cranelisp-exe-bundle` call). The platform crate stays unchanged (it correctly cannot depend on intrinsics). This is the durable DEF-6-class closure and the prerequisite for 0407.
**Proposed FIXME**: `target: /arch` — "Single shared `HostCallbacks` builder (consumer-side) to kill the JIT-vs-`--link` wiring divergence; DEF-6 root enabler + 0407 prerequisite."

### F3 — BC §5 invariant 5 says "`int` constructs `HostCallbacks` at `CompilerSession::new`" — silent on the `--link` construction site
**Severity**: Low — design-doc completeness → route to `/design`
**Files**: `design/arch/bounded-contexts.md:480`; second site `crates/cranelisp-exe-bundle/src/lib.rs:131`.
BC §5 invariant 5 describes a single `int`-side `HostCallbacks` construction at
`CompilerSession::new`. That is true for `--run`/REPL but **not** the `--link`
standalone-executable path, where `cranelisp_init_platform`
(`cranelisp-exe-bundle`) constructs its own `HostCallbacks` in the startup stub —
the very second site F2 is about. A reader reconciling the invariant against the
source finds an undocumented construction. **Fix**: `/design` notes the two
construction sites (session-time for `--run`/REPL; startup-stub for `--link`) and
that invariant 5's "once per session" holds per-mode. (If F2 lands, this becomes
"one shared builder, two call sites" and the doc simplifies.)
**Proposed FIXME**: `target: /design` — "BC §5 invariant 5: name the `--link` startup-stub HostCallbacks construction alongside the session-time one."

### F4 — `CLAdt::construct` calls the alloc-base return `payload_ptr` (misleading local; clarity)
**Severity**: Low — naming/clarity → route to `/dev`
**Files**: `crates/cranelisp-platform/src/adt.rs:216-221`.
`construct` binds `let payload_ptr = alloc_with_tag(...)` then passes it to
`CLAdt::from_raw`, whose doc says it takes the **alloc base** pointer — and
`HostCallbacks::alloc_with_tag`'s contract (`lib.rs:458`) is "Returns the **alloc
base pointer**." So the value IS the base; the local name `payload_ptr` is wrong
and contradicts both `from_raw`'s contract and the witness convention used
everywhere else (CL\* store base, add `HEAP_HEADER_SIZE` to reach payload). It is
not a bug (the value is correct), but the name invites a future editor to "fix" a
non-existent off-by-header error. **Fix**: rename to `base_ptr` (or `alloc_base`)
to match `from_raw`'s parameter name.
**Proposed FIXME**: `target: /dev` — "Rename `CLAdt::construct`'s `payload_ptr` local to `base_ptr` (alloc_with_tag returns the alloc base, not the payload)."

### F5 — Hand-authored `CLAdtType` markers; stringly-typed `TYPE_NAME` with no compiler check (LOW-3 carry)
**Severity**: Low — ergonomics/safety deferral → route to `/design` (record)
**Files**: `crates/cranelisp-platform/src/adt.rs:55-77` (rustdoc), `:72-77` (trait).
Unchanged from 06-14 LOW-3. Each marshaled ADT needs a hand-written
`impl CLAdtType { const TYPE_NAME: &'static str = "module/Type"; }`; a typo in
`TYPE_NAME` surfaces only as a runtime `resolve_field` schema-lookup-miss panic
(`adt.rs:350`), never at compile time. Acceptable in the current zero-ADT-platform
state, but the gap should be recorded so the first real ADT-marshaling platform
(the `shapes` fixture) considers a derive/macro layer before there are many
markers to keep in sync. **Fix**: `/design` records the marker-ergonomics +
stringly-`TYPE_NAME` gap as a deliberate deferral in `platform.md` (or
`platform-interface.md` §5.5 residue) and names the trigger (first multi-ADT
platform).
**Proposed FIXME**: `target: /design` — "Record the hand-authored `CLAdtType` marker ergonomics + stringly-typed `TYPE_NAME` gap as a deferred decision; revisit at the first ADT-marshaling platform."

### F6 — Fork-join error-slot ferry: the platform half (`EffectOutcome`) is sound; the join-side propagation is the open obligation (boundary note)
**Severity**: Low — cross-crate trace legibility → route to `/arch` (synthesis input)
**Files**: `crates/cranelisp-platform/src/lib.rs:688-727` (`EffectOutcome`), `:786-845` (`effect_on_resource` DLL-local catch), `:865` (`call_effect_thunk`); the open half is the intrinsics/`worker.rs` join, out of this crate.
Recorded so the §12.4.3 fork-join ferry trace is legible across crates: the
platform boundary correctly *produces* a faulted `EffectOutcome` (DLL-local catch
→ leaked cause → C-ABI return value) and the host correctly *forwards* it. The
S86-flagged swallow is downstream — whether the fork-join **join** propagates a
faulted `EffectOutcome` from a Par branch to the joining thread (vs. dropping it).
No platform-crate action; this is an intrinsics + `/arch` synthesis item. Flagged
only to connect the platform-side evidence to the open obligation.
**Proposed FIXME**: none from platform (the obligation is downstream); `/arch` synthesis correlates with the intrinsics pass.

---

## 5. Unsafe-code audit (the crate's best property — preserve it)

`unsafe` containment remains **exemplary** and is unchanged in quality from the
06-14 baseline:

- Every `unsafe` block carries a `// SAFETY:` comment naming the upheld invariant
  (heap layout, allocator contract, FFI guarantee, atomic alignment). Spot-checked
  across `lib.rs` (CL\* wrapper methods, `manifest_to_descriptors`,
  `call_effect_thunk`), `adt.rs` (`read_field`/`read_tag` offset reads), and
  `declare.rs` (`extract_layout_hash`'s ASCII-boundary slice). No `// SAFETY: trust me`.
- The `unsafe impl Send/Sync for PlatformFn` (`lib.rs:409-410`) justification
  covers each raw-pointer field (read-only `'static` data, session-bounded by
  invariant 6, multi-thread reads by the IO trampoline). Sound.
- Raw-pointer arithmetic is **contained** to the CL\* wrapper methods + the three
  `unsafe fn`s + the schema parser's byte cursor. A reader finds the whole
  `unsafe` risk surface in `lib.rs` + `adt.rs` (+ one bounded slice in
  `declare.rs`). `schema.rs` has **no** raw-pointer `unsafe` (the `from_utf8`
  paths are safe-API). No spread since the baseline.
- No `unsafe` in test code beyond exercising the unsafe boundary itself (the
  mock-heap fixtures + node-layout inspections, which is the legitimate exception).

No unsafe finding.

---

## 6. Public-surface & invariant conformance

- **Public surface** (`grep` census): `lib.rs` 37 `pub` items, `adt.rs` 10,
  `schema.rs` 13, `declare.rs` 3 (the two `#[macro_export]` macros +
  `extract_layout_hash`). Every `pub` is either the external DLL-author contract
  (CL\* family, `declare_platform!`, `HostCallbacks`, contract types) or the host
  bridge (`manifest_to_descriptors`, `platform_manifest_symbol`). No unjustified
  `pub`. The crate carries its facade in rustdoc (Principle 15 external-audience
  exception) — intact.
- **BC §5 nine invariants**: still all **Implemented/Holds** (the 06-14 table
  stands; ABI is now v6 not v5 but the invariants are version-agnostic). The
  three-exports model (GOT + manifest + schema/layout-hash) is fully emitted by
  `declare_platform!`'s two arms in `declare.rs`.
- **No work-marker FIXMEs** in source (confirmed: zero `FIXME(/…)`/`TODO`/`XXX`).
  The ~40 "FIXME NNNN" mentions are rustdoc provenance references.

---

## 7. Agent guidance / apparent traps

- **The host-callback wiring is divergence-prone by hand-mirroring (F2).** If you
  edit `HostCallbacks` or its wiring, you MUST update **both** `src/platform.rs:253`
  AND `cranelisp-exe-bundle/src/lib.rs:131` (+ the test mirror `src/platform.rs:932`)
  — there is no shared builder yet. This is the DEF-6 trap. The `def6_*` guards in
  `lib.rs` pin the platform-side invariant but cannot catch a host-side
  per-mode wiring divergence.
- **`alloc` MUST return a PAYLOAD pointer (base + 16), `alloc_with_tag` MUST
  return the ALLOC BASE.** The two host allocator callbacks have *opposite* return
  conventions by design (`HostCallbacks::alloc` rustdoc vs `alloc_with_tag`
  rustdoc). Do not "unify" them — the platform's node constructors subtract
  `HEAP_HEADER_SIZE` from `alloc`'s return but use `alloc_with_tag`'s return as-is.
- **`platform.md` says ABI v5; source is v6 (F1).** Trust `lib.rs:229` +
  `ABI_VERSION`'s rustdoc; distrust `platform.md`'s version numerals until F1 lands.
- **Do not widen `HostCallbacks` for 0407 before F2 lands.** Adding
  `rc_inc`/`rc_dec`/`invoke_closure` triples the per-mode wiring-agreement hazard;
  the shared builder is the prerequisite (§3.4).
- **The schema grammar lives in two crates but is now corpus-pinned.** Changing
  `cranelisp-backend::generate_schema`'s emit still requires mirroring it in
  `cranelisp-platform::schema.rs`, but `tests/platform_schema_roundtrip.rs` now
  catches drift — keep that test exercising the changed shape.
- **Keep `unsafe` in the wrapper family.** New raw-pointer work belongs inside a
  CL\* method with a `// SAFETY:` comment, not at a call site. This is the crate's
  best property.

---

## 8. Summary

`cranelisp-platform` entered S87 healthier than the 06-14 baseline left it:
**6 of 7 prior findings resolved** (macro extracted, R1 gate reframed, unwraps
hardened, schema-grammar drift corpus-pinned, "no runtime state" phrasing
corrected), one **partially regressed to a fresh one-bump doc staleness** (F1, ABI
v5→v6), and one **deferred as designed** (F5, marker ergonomics). The interior
7 lenses (i)–(vi) are clean; `unsafe` discipline is exemplary and unchanged.

The **headline is lens (vii)**: the JIT-vs-`--link` host-callback divergence is
**real and structural** — not because the platform crate is wrong (it is the
correct, dependency-clean contract definition) but because the *consumers* wire
the contract by hand-mirroring at two production sites with **no shared builder**.
DEF-6 was the allocator instance of that gap; **FIXME 0407 is the
closure-callback instance of the same family** and will multiply the hazard. The
durable closure (F2) is a consumer-side single `HostCallbacks` builder — an
`/arch`-synthesis item, prerequisite for safely landing 0407. The layout-hash
export path (§3.3) shows the divergence-proof-by-representation shape the
callback wiring should adopt.

**Findings**: 0 HIGH · 1 Important (F2, lens-vii headline, route `/arch`) ·
2 Medium-ish doc-currency (F1 `/design`; F3 folded as Low `/design`) ·
3 Low (F3 `/design`, F4 `/dev`, F5 `/design`) · 1 boundary note (F6, `/arch`
synthesis input). Prior-findings status: **6 resolved, 1 deferred** (of 7).
