# The ownership stratum — structural options

**STATUS: OPTION PAPER (S118 deliverable, user-commissioned 2026-07-26; feeds
S119 Phase 1).** This paper decides nothing. It lays out the structural options
for the manual reference-counting stratum — evidence, mechanisms, costs, staged
paths, composition — and states a recommended S119 shape. **The user decides**
(§7). Archive trigger: the user's S119 Phase-1 disposition lands and each
adopted option's binding contract moves to its own manifestation site
(per-crate design docs, `safety-invariants.md`, `tests/plan/`, `principles/`);
this file then archives as the decision record.

**Commission.** After three sprints (S116–S118) in which nearly every execution
failure concentrated in one stratum, the user asked whether tooling,
restructuring, or modularity changes are needed to make the code manageable.
The shared diagnosis (`sprints/SPRINT.md` §Notes 2026-07-26): the stratum's
**cost structure** — not the process, and not the codebase broadly — is the
systemic reliability problem. The big decisions are made on paper, not
mid-wave.

---

## 1. Problem statement — the stratum and its cost structure

### 1.1 What the stratum is

Manual reference-counting discipline lives in exactly two places, with the
contracts that bind them living in a third:

1. **The hand-written runtime pair** — `cranelisp-primitives` (marshal, string,
   Vec adapters) + `cranelisp-intrinsics` (alloc/RC/drop funnels, `consume_*`
   glue; `drop.rs` alone is 735 lines). The pair exposes ~83 `extern "C"`
   functions, and heap values cross every one of these seams as **raw `i64`**
   — roughly 131 function signatures in the pair take at least one `i64` that
   is really a heap handle, and ~31 call sites in primitives invoke a
   `consume_*`.
   Whether a given `i64` parameter is *consumed*, *borrowed*, or *stored* is
   stated nowhere the compiler can see.

2. **Backend RC emission** — the generated code's inc/dec arithmetic, shaped by
   special cases: move/COW exemptions, borrowed-alias elision, TCO
   carry-forward, match-scrutinee release gates, capture teardown. Until W3
   completes, five distinct glue mechanisms coexist
   (`design/backend/transitive-drop-glue.md` §1.1 M1–M5).

3. **The contracts, in prose.** The primitives ownership facts are
   declaration-table rows; the consuming convention is rustdoc; the embed rule
   was (until W2b) a rustdoc paragraph — one that **documented the defect as
   intent** ("It gets a deep RC inc (every SCons node and every element)").
   Both recent audits converge on this: `audits/cranelisp-primitives-s116.md`
   grades code Strong-to-adequate but finds the highest-risk declared ownership
   facts "tested as declarations, not checked against production emission";
   `audits/cranelisp-platform-s117.md` grades code Strong and realisation
   **Weak** — the prose describes retired and current architectures
   simultaneously.

### 1.2 The S116–S118 record — where the failures actually were

- **0835 / RE-1 (S118 W2b)** — `marshal::deep_rc_inc_slist` inc'd every node
  and element of an embedded tail where the ownership model licenses exactly
  one inc. **Entirely safe Rust**: no unsafe-block audit could have flagged it,
  and the rustdoc blessed it. Cost per call: `2|ys| + 2` atomic RMWs where the
  correct count is `2`; the fix was a strict reduction. It leaked on every
  macro expansion for at least three sprints.
- **The masked double-free beneath it (W2b D0–D4).** The pre-fix detector arc
  settled the abort face as candidate (i): the surplus references were
  *masking* a co-present premature free. M1 quarantine made the abort
  disappear pre-fix (write into a reused freed chunk); M2 poisoning exposed a
  use-after-free read two chained `sconcat` up (FIXME 0815's `match failed`
  symptom, reproduced under detection, present in `--run` too). Post-fix, the
  armed lane **located** the surviving face: `STALE RC DEC (JIT inline)`
  double-releasing a one-byte `HeapString` extracted under a constructor
  pattern — the 0810-B/0782 **backend emission** family, exactly as the design
  predicted. One seam, two defects, in the two halves of the stratum, each
  hiding the other.
- **The macro-turn marshal leak (Branch F, FIXME 0889).** The ambient 1,143
  allocations per stdlib session are a *by-design* compile-time leak at the
  int-side macro-turn boundary: marshalled argument trees never dec'd,
  expansion results never consumed — because the aliasing between result and
  argument trees makes naive release a double-free (the FIXME-0638
  interior-alias history: it has burned once already). The prose-contract
  problem in its purest form: the leak is *documented* in `src/marshal.rs`'s
  header, and no instrument owned it until S118's probe ladder derived its
  closed-form model.
- **The W1 five wrong-reason REDs.** Five baseline defect guards were failing
  behind stale pre-S116 syntax — parse errors masking the real signatures.
  Guards that fail for the wrong reason are indistinguishable from working
  guards until someone reads the stderr.
- **The 0810 family (×10), 0782, 0688, 0760/0796, 0745** — the entire Track-B
  RED clearance is emission-side release arithmetic: scrutinee lifetimes,
  var-pattern release gates, TCO replacement, capture teardown, program-result
  ownership. Every one is a special case in the emission where the arithmetic
  went wrong.
- **The D1 as-built drift (S116→S118).** The S116 canonical `DropGlueRegistry`
  passed review and its static checks, yet **could never have run as
  designed**: the registry held `&mut M` while `FnCompiler` holds `&mut M`
  (both cannot exist), and the registry was `finish()`ed before body
  compilation ran — no consumer could ever have requested glue. Two sprints of
  static-only PASS on a mechanism with zero executions. Nothing in the
  stratum's verification regime executes an ownership mechanism as a matter of
  course; only consumers do, and the consumers hadn't migrated.
- **The W2a precheck-hoist discovery (§7.5).** All four env-gated seam checks
  ran *after* their mutation and after always-on `debug_assert!` twins — in
  the debug profile a planted fault tripped the twin before reaching the gate,
  so positive detection proofs would have failed against *working* detectors.
  Even the instruments needed instruments: the S118 rule that "an instrument
  is unverified until it is proven to detect" (METHOD §2.2, FIXME 0768) exists
  because assertion of capability was repeatedly wrong here.

### 1.3 The blind-spot pattern — why the tests could not see any of this

Three findings share one structure:

- `decision24_sconcat_rc_balanced` — the seam's ONE unit row used a one-cell
  tail with bare-tag elements: `over-incs = (1−1) + 0 = 0`. The single sampled
  point sat exactly where the defect is arithmetically invisible.
- **0867** — field accessors are minted for products only; every prior guard
  used the one spelling that works (same-name constructor arm), so every sum
  type and distinct-name product silently lacked accessors. A
  coverage-by-definition-variants miss: the corpus exercised the author's
  spelling.
- **0885 (delegated review finding)** — the W2b inc-count fence, as first
  committed, was verified *by arithmetic* to pass under the §3-**rejected**
  move-variant: the fence pinned the balance but not the ruling. The fix was
  to assert the inc *tally* (`|xs| + 1`), not just the residual.

The structural property: **example-based tests sample points, and the sampled
point is chosen by the same understanding that wrote the code** — so a test
written against the same wrong model passes at exactly the points the model is
wrong about the same way. `safety-invariants.md` §2 already states the
consequence ("example-based testing and adversarial review are discovery, not
checks"). The options divide accordingly:

- **Options 1 and 2 attack representability** — make the wrong count
  *unwritable* (typed handles) or *unemittable* (uniform emission). A class
  with no representation needs no test to be absent.
- **Options 3 and 4 attack measurement** — make the instrument read the
  quantity the cell names (marginal accounting), assert the *rule* rather than
  a sample point (the inc-count/rate fences; a per-value-path pairing check),
  and reject at emission time rather than observe at runtime.

Both are needed; neither substitutes for the other.

### 1.4 What review contributes — and what it cannot

Two delegated cross-model reviews ran in S118 (W2a, W2b). Both found real
findings — 0880 (missing per-site `// SAFETY:` comments, 11 flagged / 27
fixed), 0885 (the fence-vs-ruling gap above), 0884 (safe helpers with
provenance-inferring SAFETY comments) — and both times the **production change
was clean**. Review here is functioning at a high level and is still the last
line of defence, not the first: the S111 register (§1 of
`safety-invariants.md`) records that every memory-safety defect of that sprint
was found incidentally, and S116–S118 repeated the pattern. More review effort
is not the lever; the lever is what the code can express and what the
instruments can see.

### 1.5 The cost structure, stated

Every hand-written seam pays: (a) a prose contract someone must re-derive at
every call site; (b) a raw `i64` that type-checks identically whether the
count is right or wrong; (c) an outside-process count-based test whose
baseline was, until S118, not even truthful. Every emission special case pays:
(d) one more place where release arithmetic is locally decided; (e) an
interaction surface with every *other* special case (the scrutinee gate × the
COW exemption × TCO). The defect record is the integral of these costs over
three sprints. The options below each remove one term.

---

## 2. Option 1 — typed handle discipline in the runtime pair

### 2.1 Mechanism

Newtype the raw `i64` heap handle **inside** the runtime pair. The C-ABI/JIT
surface is untouched: `extern "C"` signatures keep `i64`; the typed layer
begins at the extern shim.

- `Owned(i64)` — a counted reference the holder must discharge. `#[must_use]`,
  no `Copy`/`Clone`; a debug-profile drop-bomb (`Drop` that panics unless
  explicitly discharged) makes "leaked on the floor" a located failure at the
  exact frame. Discharge = pass by value into a consuming fn (`consume_*`, a
  store into a structure, return across the ABI shim).
- `Borrowed(i64)` (or `&Handle`) — `Copy`, read-only access, no discharge
  obligation, cannot be stored (storing requires `.to_owned()`, which is the
  one place `rc_inc` lives).
- Transfer is the *signature*: `fn sconcat(xs: Owned, ys: Owned) -> Owned`
  says the Decision-24 consuming convention in code;
  `fn slist_len(l: Borrowed) -> i64` says the borrow. The shim annotations
  come from the primitives declaration-table ownership facts (invariant 4) —
  one source, two manifestations, checkable against each other.

**Precedents already in-tree, both silent since landing:**

- The **S117 Vec-of-String boundary** (`vec_strings_from_owned(Vec<i64>) ->
  i64` + `with_vec_strings(base, callback)`): construction transfers owners
  exactly once and unwinds partial ownership exactly once; the read view is a
  callback-scoped borrow that *cannot escape in safe Rust*. Ownership encoded
  in the signature shape — zero defects on that boundary since S117.
- The **platform crate's `CLOwned<T>`** (BC §5): host-side RAII over the same
  `i64` ABI, transfer at the callback contract. The external surface has run
  this discipline for many sprints.

Option 1 is the generalization of these two proven boundaries to the rest of
the pair.

### 2.2 What it makes unrepresentable — mapped to the record

- **The RE-1 class (0835).** `deep_rc_inc_slist` mints `n + h − 1` references
  no owner holds. Under typed handles, every `.to_owned()` yields an `Owned`
  that must be *stored or discharged*; a walk minting owners it cannot store
  produces drop-bombs (debug) and `#[must_use]` warnings (always). The
  over-inc stops being a number someone must audit and becomes a value with
  nowhere to go.
- **Double-discharge.** Passing an `Owned` to two consumers is a move-checker
  error. The hand-written analogue of 0782's shape cannot compile.
- **The prose-contract term (§1.5a–b).** The consuming convention stops being
  rustdoc a caller must remember; `cargo check` enforces it at every call
  site, including future ones. This is Principle 18 (enforce invariants
  structurally) and Principle 20 (model invariants by representation) applied
  to the one surface that never received them.

**Honest limits.** Rust cannot enforce *exactly-once* fully — `mem::forget`
and early-return paths around a drop-bomb exist; the shim layer can lie (an
extern wrapper that wraps a borrowed param as `Owned` mis-declares just as
prose can). The discipline narrows the trusted base from "every call site in
two crates" to "the shim annotations + the newtype impl" — a large reduction,
not an elimination. The shim annotations must be generated from or checked
against the declaration-table facts, not hand-written twice (Principle 7).

### 2.3 Staging — boundary-by-boundary, each tranche independently shippable

> **S119 Phase-2 amendment (`/arch`, 2026-07-26; resolves FIXME 0920).** The
> original tranche-B row conflated two files: "339 lines" measured
> `crates/cranelisp-primitives/src/marshal.rs` (runtime `quote_sexp`/`sconcat`
> helpers — inside the pair, but NOT where the 0889 leak lives), while "the
> macro-expansion data path" and the §6.3 recovery claim describe
> `src/marshal.rs` (732 lines) + `src/expander.rs::invoke_clause` — the **int
> binary**, which §1.1 excludes from the pair. The rows below are the corrected
> scope. The typed vocabulary needs no third home: tranche A already forces
> `Owned`/`Borrowed` to be `pub` from `cranelisp-intrinsics` (the `consume_*`
> fns are `pub` and the types appear in their signatures — the Principle-15
> home, since the discharge behaviour lives there), and both primitives (an
> existing dependant) and the int binary consume that one vocabulary. Sizing
> figures re-pinned against measurement 2026-07-26: **83** `extern "C" fn`
> (intrinsics 81 + primitives 2), **136** non-extern `i64`-taking fn
> declarations, **36** `consume_*` call sites in primitives (`string.rs` 27,
> `marshal.rs` 8, `int.rs` 1).

1. **Tranche A — the drop/consume funnel** (`cranelisp-intrinsics::drop` +
   its 36 primitives call sites, which include
   `crates/cranelisp-primitives/src/marshal.rs`'s 8). Smallest,
   highest-leverage: every `consume_*` signature becomes
   `fn consume_slist(l: Owned)`, and every caller's obligation becomes
   visible at once.
2. **Tranche B — the int-side macro-turn marshal boundary**
   (`src/marshal.rs`, 732 lines, + `src/expander.rs::invoke_clause`). This
   tranche **is** the FIXME 0889 recovery vehicle (§6.3): typed handles
   force the argument-tree and result-tree counts to be right, after which
   the turn's release is plain `consume` — `consume_slist` already stops at
   live shared references, so correctly-counted trees release correctly
   without aliasing analysis. It is a **third typed surface** outside the
   pair: `/design`(int) rules the marshal/expander ownership protocol before
   any `/dev` dispatch (0889's own precondition), consuming the intrinsics
   vocabulary; `/arch` holds the boundary question. Sequenced strictly after
   tranche A — the vocabulary must exist and be consumer-proven first.
3. **Tranche C — string/Vec adapters** (the remaining i64-taking internal
   fns of the 136, including the primitives-side `marshal.rs` helpers not
   already covered by A's consume-site flips), aligning with the
   already-typed S117 Vec-of-String boundary.
4. **Tranche D (optional, later)** — align the internal newtypes with the
   platform `CLOwned` family naming so the two typed layers read as one
   discipline. Doc-level only; no ABI change.

Each tranche: signatures flip, `cargo check` enumerates every affected call
site, the existing unit rows (now including the RE-1 fences) pin behavior
unchanged. No `CACHE_SCHEMA_VERSION` impact, no `cranelisp-types` impact, no
generated-code impact. Public-API delta confined to the pair's
`public-api.txt` where signatures are `pub` (most of the marshal surface is
`pub(crate)` behind extern symbols — the extern names and ABI do not change).

### 2.4 Cost and risks

- **Cost estimate:** 83 extern shims + 136 internal signatures (re-pinned;
  see §2.3 amendment), mechanical per-site with the compiler enumerating the
  worklist. Tranche A is a focused `/dev`(runtime pair) wave; tranche B is an
  int-surface wave with its own `/design`(int) protocol ruling (larger than
  originally priced — 732 lines plus the expander seam); C similar to A.
  Order three dev waves total, review per tranche. No user-visible change.
- **Risk: churn masking a behavior change.** Mitigated by the S118 instrument
  set: every tranche re-runs the marginal cells, the RE-1 fences, and the
  armed-lane rows byte-identically — the same invariance discipline 0850's
  convergence used.
- **Risk: ergonomic drag in the pair.** Real but priced: the pair is exactly
  where three sprints of failures concentrated; friction that makes a
  transfer explicit is the point.
- **Risk: false confidence at the shim.** §2.2's honest limit; the shim-fact
  single-sourcing is the mitigation and must be part of tranche A's design.

---

## 3. Option 2 — uniform-but-redundant RC emission

### 3.1 Mechanism

Collapse the generated-code special cases — move/COW exemptions, borrowed
aliases, TCO carry-forward, match release gates, control-flow protection —
into **always-inc/dec** emission in the dev/JIT tier: every binding
occurrence incs, every scope exit decs, every replacement releases the old
owner, uniformly, with no per-construct arithmetic. Elision becomes an
optimization the `--release` tier performs under a verification guard.

The architecture already names this lowering: it is the **conservative
all-Owned lowering** that `ownership-inference.md` §2.1/R7 keeps permanently
reachable as the differential oracle, and that Principle 25 defines as **the
reference semantics** ("the conservative all-Owned lowering IS the definition
of correct behavior for the memory model; an elision is correct iff
equivalent to it" — `safety-invariants.md` §3d). Option 2 promotes the
reference semantics from oracle to **default dev-tier emission**: the thing
you run is the thing that defines correctness; the optimizer tier must prove
equivalence to it (R9's standing lane is exactly that gate, already landed
and PROVEN with a live catch).

### 3.2 What it would have prevented — mapped to the record

Each special case is a place to be wrong, and each has been:

- **0810 (×10 faces)** — match-scrutinee lifetime decided per-arm-shape; under
  uniform emission the scrutinee incs at bind and decs at scope exit like any
  binding; the ten faces collapse into the one general rule.
- **0782 / the located `STALE RC DEC (JIT inline)`** — the var-pattern release
  gate double-releasing an owned temporary; there is no gate to get wrong.
- **0688-family TCO** — carry-forward is an elision (skip the release because
  the owner moves forward); uniform emission releases and re-incs, trivially
  correct, and the optimization moves to the tier with the guard.
- **The masking phenomenon itself (§1.2).** Redundant-but-correct counts mean
  a leak is a leak and a double-free is a double-free — the W2b experience of
  one defect's surplus references hiding another's premature free is a
  property of *tuned* counts being load-bearing.

What it does **not** address: the hand-written pair (option 1's territory),
and identity/keying defects (0633/0640 — R4's territory).

### 3.3 The performance question — the honest numbers

The cost is atomic-RMW traffic in the dev tier. The record gives both
directions:

- The W2b fix showed redundant traffic is not noise: removing one redundant
  deep inc cut per-embed traffic **`2|ys|+2 → 2`**. Uniform emission spends in
  the opposite direction at every binding.
- S94's floor-scope ruling (`effect-concurrency.md` §3.1): allocation-/RC-heavy
  **parallel** workloads violated the "never dramatically slower" floor by up
  to ~10× from atomic-RC contention — with today's *partially* elided
  emission. Uniform emission increases the term that ruling already flagged.

For the dev tier's actual workloads — REPL turns, `--run` of tests/examples,
macro expansion — the traffic is sequential and bounced-line contention is
absent; the honest expectation is a measurable constant-factor cost, not a
cliff, but **no measurement exists yet**. If the user takes this option, the
first act is a measurement gate: the marginal harness's twin-control shape
over uniform-vs-current emission on the exemplar and the suite, before any
commitment to ship.

### 3.4 Interaction with W3 (binding)

W3 — the ownership consumers migrating onto canonical glue, with the atomic
five-mechanism deletion — **proceeds regardless and is not gated on this
option** (arch ruling 10 stands; the P8 bridge closes in S118). Option 2 is
about *inc/dec site arithmetic*; W3 is about *glue identity and dispatch*.
They compose: uniform emission wants exactly one glue to call, which is what
W3 delivers. Sequencing if adopted: option 2 lands **after** W3, as a second
emission change over the collapsed mechanism — never interleaved with it.

### 3.5 The release-tier elision path

Adopting option 2 re-stages `ownership-inference.md`: increments I/II (borrow
inference, uniqueness/reuse) stop targeting the dev tier and become the
`--release` optimizer's input, verified by the R9 differential lane plus
(if option 4 matures) the emission-side audit. Monotone soundness is
unchanged — the analysis was always allowed to be wrong only toward Owned;
now the dev tier simply *is* the all-Owned point. This is the main reason the
option is a **user decision**: it re-sequences a ratified subsystem design
and trades dev-tier performance for the permanent removal of the emission
special-case defect class. It is reversible in principle (the special cases
could be re-introduced tier-by-tier under P25 checks) but expensive to
reverse in practice.

---

## 4. Option 3 — the marginal-balance harness, generalized

### 4.1 Status: a working first instance exists

`tests/helpers/marginal.rs` landed 2026-07-26 with a three-cell capability
fence (`tests/marginal_harness_capability.rs`), deliberately built as the
first instance of this option: control/subject child pairs differing in
exactly one axis, `env_clear` + enumerated allow-list, per-child instrument
arming, and the marginal `subject.residual − control.residual` as the
asserted quantity. Four baseline cells flipped GREEN **on real measurements**
(none by construction); the 0889 pins hold the documented leak at exact
closed-form values so any drift or half-fix flips a pin. The
load-bearing capability fact: two independent full-stdlib children report an
*identical* ambient residual, so the subtraction is exact, not approximate.
`tests/CLAUDE.md` already carries the rule ("allocator balance is measured
MARGINALLY, never absolutely") for the e2e tier.

### 4.2 The generalization — what remains to decide and build

1. **Per-crate unit-tier adoption.** The blind decision24 row was a unit row;
   the harness is e2e (subprocess pairs). The unit-tier form already exists
   embryonically in the W2b RE-1 rows: *rule-shaped* assertions against the
   in-process counters — the rate property (residual independent of `|ys|`),
   the inc-count fence (tally = `|xs| + 1`, pinned against the rejected
   variant per 0885). Generalization = a small in-crate helper (delta-vs-
   control over the RC/alloc counters around a closure) plus a `/qa` lens rule:
   a unit row asserting balance at one point is the anti-pattern; assert the
   rule's *shape* (a rate, a tally, a marginal) or add the variant axes.
2. **The cold/warm cache axis (FIXME 0890).** Cell #21's threshold is ~87%
   ambient; the re-derivation must warm the control identically to the
   subject (cold-then-warm without `--no-cache`). The harness needs a warmed-
   pair mode; 0890 owns the acceptance-arithmetic ruling at W3.
3. **Threshold-cell retirement.** Every remaining absolute/threshold balance
   cell re-derives marginally or records why not (0890 is the worked
   instance).
4. **Normative form for the leak lanes — a `/qa` co-owned question.** Whether
   the marginal pair becomes *the* normative leak-lane form (in
   `tests/plan/`, R8's lane row, and the certification split) is `/qa`'s
   authority over lane mechanics with `/arch` owning only the register
   linkage. This paper flags the question; it does not answer it.

### 4.3 What it addresses, cost, risks

Addresses **measurement blindness**, not representability: cells finally
measure what their names claim (the four flipped cells were red on a term
their workload did not produce), and rule-shaped assertions close the
sampled-point blind spot that hid RE-1 for three sprints. Cost: a marginal
cell is two children (~2× an absolute cell) — cheap; the unit-tier helper is
small. Risk: the control axis must genuinely differ in one thing only — the
harness enforces this by construction at e2e; the unit-tier helper must
preserve that discipline. Composition: option 3 is the *acceptance
instrument* for options 1 and 2 (every tranche and every emission change
re-runs the marginal cells as its invariance pin) and it is already
mandatory-in-place for S118 W3/W4.

---

## 5. Option 4 — emission-side balance audit (design spike)

### 5.1 Mechanism sketch

A debug-mode pass over emitted CLIF (or over the backend's own emission
events, which is likely the better seam — the emitter knows *why* each
inc/dec exists) checking inc/dec pairing per value path, moving detection
from runtime observation (M-detectors, RC_STATS — after the fact, input-
dependent) toward emission-time rejection (before execution, input-
independent).

### 5.2 What static pairing analysis can and cannot see — honestly

**Can see, per-function, cheaply:**

- a dec with no same-path ownership source — the `STALE RC DEC (JIT inline)`
  shape the armed lane caught at runtime in W2b;
- double-dec of one value on a single path (0782's shape);
- a scope exit that releases a slot already transferred on that path.

**Cannot see without whole-program facts it does not have:**

- **control-flow joins** — a value released on one arm and carried on
  another is exactly the 0810 per-arm territory; path-sensitive verdicts at
  joins need the same analysis whose absence is the problem;
- **escapes** — a store into a structure transfers the obligation to drop
  glue in another function; pairing is inter-procedural;
- **TCO** — the obligation crosses iterations by design;
- **closure captures** — release deferred to capture drop glue.

So a sound-and-complete audit is equivalent to the ownership analysis itself;
the honest target is a **conservative linter for the locally-decidable
subset**, hard-failing in debug on the shapes it can prove wrong. Notably:
**if option 2 is adopted, the undecidable cases largely vanish** — uniform
emission makes pairing local by construction, and the audit's job collapses
to verifying the release tier's elisions (where it becomes the static
companion of the R9 differential lane).

### 5.3 What S117 W4b already provides, and the spike's scope

W4b landed nine ownership witnesses (five production-CLIF + four mode twins)
plus two transfer units: **sample-based** evidence that declaration mutations
change emission through the real path. They are mutation witnesses, not a
pass — they prove sensitivity at chosen points, with 0859's ProjectionOf
production shapes emission-inert and explicitly deferred. The spike's
questions, scoped for one `/design`(backend) deployment:

1. enumerate the emission-event facts available at the natural seam (the
   `emit_typed_rc_dec`/glue-call sites post-W3);
2. prototype the local checker over the golden-CLIF corpus (S102's lane);
3. classify the S116–S118 defect ledger: which would the checker have
   rejected at emission time (predicted: 0782 yes; the stale-dec face yes;
   0810 joins partially; 0688 no);
4. report cost/coverage so the user can decide build/park with numbers.

Deliverable: a spike report, not a mechanism. Risk of skipping the spike:
committing to a pass whose reachable coverage is the subset the runtime
detectors already cover well.

---

## 6. Composition and the recommended S119 shape

### 6.1 How the options compose

| | Attacks | Half of the stratum | Depends on |
|---|---|---|---|
| 1 — typed handles | representability | hand-written pair | nothing (W3-independent) |
| 2 — uniform emission | representability | generated code | after W3; re-stages ownership-inference |
| 3 — marginal harness | measurement | both (instrument) | landed; generalizing |
| 4 — emission audit | measurement→rejection | generated code | spike first; shrinks if 2 adopted |

1+3 are independent, cheap-to-medium, and cover the half of the stratum where
S118's confirmed root causes lived (RE-1, the marshal leak) plus the
instrument layer everything else is accepted against. 2 is the
high-consequence decision covering the other half (where W3's RED family
lives) and carries a real performance trade. 4's reach is genuinely uncertain
until the spike runs.

### 6.2 Recommended S119 shape

The commission asks this recommendation to be tested rather than inherited
from `/sprint`'s prior. Tested against §1's evidence, it holds, with one
sharpening (the 0889 routing) and one sequencing caution:

- **Core: option 1, tranches A + B** (`/design`(runtime pair) contract, then
  `/dev` per tranche) **+ option 3 generalization** (unit-tier helper +
  `/qa`'s normative-form ruling + 0890's re-derivation). Rationale: these
  close the S118-confirmed root-cause classes at the representability level,
  are independently shippable, carry no schema/ABI risk, and the instrument
  half is already proven in production use.
- **Option 4 as a bounded design spike** (one `/design`(backend) deployment,
  report-only), sequenced after W3 so the surveyed seam is the collapsed one.
- **Option 2 as a user decision on this paper**, with the measurement gate
  (§3.3) as its first act if taken, and landing only after W3 in any case.
  The recommendation is to **decide the direction now but gate the commitment
  on the measurement** — the option's value is high and its cost is the one
  number nobody has yet measured.
- **Sequencing caution:** S119 also carries the descoped Tracks C/D/E. The
  core above is deliberately sized so the ownership work does not again
  consume the sprint: tranche A+B and the option-3 items are each single
  narrow waves with existing acceptance instruments.

### 6.3 FIXME 0889 routing (the user-required leak recovery)

Route the recovery **through option 1 tranche B** (the int-side macro-turn
marshal boundary, `src/marshal.rs` + `src/expander.rs::invoke_clause` — per
the §2.3 S119 Phase-2 amendment):
typed handles force the argument-tree and result-tree counts to be truthful
at marshal time, after which the macro-turn exit is plain
`consume`-per-tree — `consume_slist` is already alias-correct (it stops at
live shared references), so the 0638-class double-free danger is exactly the
*miscounting* that tranche B eliminates, not a property of releasing per se.
The arena/epoch turn-allocator alternative (reclaim the whole expansion turn
wholesale) is the **fallback** if tranche B's accounting proves intractable:
it is strictly more machinery (a second allocation regime threaded through
the shared alloc funnel and the detector ledger) and its wholesale-reclaim
model must still answer which turn objects escape (expansion results copied
via `runtime_to_sexp` do; anything retained by the session must not be in
the arena). Acceptance either way: the 0889 exact-value pins flip from
documented-residual to zero; the marginal instrument stays valid unchanged.

---

## 7. The user-decision list (stated neutrally)

1. **Option 2 — adopt, reject, or defer-pending-measurement?** Adopting makes
   the conservative lowering the dev-tier default and moves all elision to
   `--release` under the existing differential guard; it removes the emission
   special-case defect class and re-stages `ownership-inference.md`; it costs
   dev-tier performance by an amount not yet measured (§3.3's gate would
   produce the number first). Rejecting keeps tuned dev-tier emission and its
   special cases, with W3's mechanism collapse and options 3/4 as the
   mitigation. Deferring keeps the question open at zero cost until the
   measurement exists.
2. **The S119 core — approve option 1 (tranches A+B) + option 3
   generalization as scoped in §6.2?** This is scope approval; the
   per-tranche contracts go through the normal Phase-3 design gates.
3. **Option 4 — authorize the bounded spike?** Report-only, one deployment,
   after W3.
4. **FIXME 0889 recovery path — via option-1 tranche B (recommended), or the
   arena/epoch turn allocator directly?** §6.3 states the trade.
5. **Normative leak-lane form** — whether the marginal pair becomes the
   required form for all balance lanes is `/qa`'s to propose (lane mechanics
   are plan-owned); the user arbitrates only if `/qa`'s proposal changes the
   certification split's meaning.

## 8. Rejected alternatives (assessed, not strawmanned)

- **Big-bang restructuring** (merge/re-cut the runtime crates; replace RC
  with a tracing GC; rewrite the pair wholesale). The audits grade the
  *boundaries* Strong — a second implementation would keep the severed
  primitives leaf, the intrinsics funnels, and the platform ABI crate. The
  failures live in the discipline *within* the boundaries, which options 1–4
  address in place. A GC swap is a different language commitment
  (deterministic RC teardown is load-bearing across the drop-glue/`--link`
  architecture and the spec's runtime model) and is not priced for Phase H.
  Restructuring cost would be catastrophic mid-release-push for no targeted
  defect-class removal.
- **Safe-Rust-everywhere** (eliminate `unsafe` from the pair as the goal).
  The premise fails on the record: **RE-1 was safe Rust** — `rustc`'s memory
  safety does not check *count* correctness, which is the actual failing
  property. Unsafe is already concentrated at the layout seams (both audits),
  and the raw heap ABI shared with JIT-emitted code makes some unsafe
  irreducible. The 0880/0884 findings show the real discipline need is honest
  contracts *around* unsafe — which option 1 supplies structurally. Pursuing
  zero-unsafe would spend the S119 budget on the property that was not
  failing.
- **A heap-header type/drop word** (make every allocation self-describing so
  a generic releaser exists). Already rejected with rationale at R15 / BC
  §4b invariant 16: it taxes every allocation and changes the heap
  ABI/cache representation to solve a finite, enumerable set of typed
  displacements that already carry their types. Restated here only because a
  uniform-emission discussion tends to resurface it.
- **Status quo + more instance-patching.** The three-sprint record is the
  argument: each patched instance (CS-1.1→0640, CS-5→0641, the decision24
  row→RE-1) needed an adversarial follow-up to find the next layer. The
  register's own conclusion — the mechanism, not the instance, closes a
  class — is the reason this paper exists.

## 9. Cross-references

- `sprints/SPRINT.md` — the S118 record this paper cites throughout (W1
  findings, W2a/W2b arcs, Branch F, the commission text).
- `design/runtime/s118-structural-embedding-ownership.md` — RE-1/RE-2/RE-3;
  the D0–D4 detector arc design.
- `design/backend/transitive-drop-glue.md` §1.1/§3.4 — the five-mechanism
  census and D1–D9 as-built reconciliation.
- `design/arch/safety-invariants.md` — the ladder, the register (R16 is
  RE-1's row), Principle 25's frame.
- `design/arch/ownership-inference.md` + `principles/25-*.md` — the
  conservative-lowering reference semantics option 2 promotes.
- `tests/helpers/marginal.rs` + `tests/CLAUDE.md` §"Allocator balance…" —
  option 3's landed first instance and its e2e-tier rule.
- FIXMEs 0889 (leak recovery — §6.3), 0890 (threshold re-derivation),
  0867 (the variant-coverage miss).
- `audits/cranelisp-primitives-s116.md`, `audits/cranelisp-platform-s117.md`
  — the prose-contract evidence.

## Next skills

- **USER** — the §7 decision list, at S119 Phase 1.
- `/sprint` — fold the dispositions into the S119 plan.
- `/design` (runtime pair) — tranche-A/B contracts if §7.2 approves.
- `/qa` — the option-3 normative-form proposal + 0890.
- `/design` (backend) — the option-4 spike if §7.3 approves, after W3.
