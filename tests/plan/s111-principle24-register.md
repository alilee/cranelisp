# S111 Principle-24 classification battery + compiler-wide register (/qa, 2026-07-17)

The verification lane scheduled at S110 close (Principle 24 "Resolve once",
RATIFIED 2026-07-16): classify **every unindexed iteration compiler-wide** as
enumeration (legit) or identity-scan (defect). This file is the battery (the
criteria, transcribed verbatim from
`design/arch/principles/24-resolve-once.md`) and the register (site → verdict
→ grounds). `/qa` owns the register and attribution of findings; `/audit`'s
frontend-rotation assessment carries the frontend leg in depth (its
§2.1-style verification section); backend is CITED from the s110 audit, not
redone. Read-only — no design artefact; the principle file IS the criterion.

## 1. The battery

### 1.1 The acid test (verbatim)

> *Does the answer depend on which entries happen to be present elsewhere, or
> on the order a collection iterates?* If yes, it is an ambient scan, and its
> result may not become an identity the compiler acts on. A chain's step
> order is a function of the program text (scope precedence, the fetched
> entry's pointer); a scan's order is incidental (hash order, insertion
> order, directory order) — dependence of the answer on incidental order IS
> the divergence surface.

Two-part application per site: (a) does the result flow into a
**compile-necessary identity** (a name, a type, a member, a dispatch target
the compiler acts on)? If no → out of scope (display/stats/persistence
walks). If yes: (b) apply the order-dependence test.

### 1.2 Carve-out 1 — enumeration is not a search (verbatim, operative clause)

> Reading ALL rows of an indexed set … is a complete-by-construction read
> whose answer is a function of the complete set, hence order-independent.
> Its failure mode is *incompleteness* … never divergence. … The discipline
> that keeps an enumeration on the right side of the line: the consumer uses
> the COMPLETE set, and **a tie is an ambiguity error, never broken by
> iteration order. An enumeration that returns the first match of a
> many-candidate set has become a scan.**

Verification obligations for an "enumeration" verdict: (i) complete set
consumed (one reader per kind, every source contributes rows or a legal skip
— `resolve-home-enumeration.md` §3); (ii) tie discipline stated and
structural, or the uniqueness invariant that makes ties impossible is
documented; (iii) no early-exit-on-first-match over a many-candidate set.

### 1.3 Carve-out 2 — `/search` (verbatim, operative clause)

> The one sanctioned genuine scan in the compiler is `/search` — … it
> produces candidates for a human to read, never an identity the compiler
> acts on. … Any future mechanism claiming the same license must satisfy the
> same criterion — human-facing candidates only, REPL-only — and be named
> here.

D1 (introspection-is-REPL-only) draws the same boundary: display/harvest/
introspection reads are non-identity by construction *provided* their result
never feeds resolution.

### 1.4 Grep classes (the sweep's search surface)

1. `symbol_tables.iter()` (the highest-signal class — the 0583 lineage)
2. `.iter()` / `.values()` / `for` over module maps and per-module tables
3. DashMap walks (any `dashmap` iteration)
4. Directory walks feeding resolution (lib-dir scans, importable-index feeds)

Classes 2–3 are pre-filtered by acid-test part (a): the overwhelming majority
are local-collection iterations (args, params, arms) with no identity flow —
only map-over-modules/tables sites enter the register.

### 1.5 Verdict vocabulary

| Verdict | Meaning |
|---|---|
| `chain` | keyed-lookup chain (the sanctioned resolver shape — explicit-pointer follows, scope precedence, prelude fallback) |
| `enumeration` | carve-out 1; grounds must state completeness + tie discipline |
| `search` | carve-out 2 (`/search` only, or D1-bounded human-facing discovery) |
| `non-identity` | fails acid-test part (a) — result never becomes a compile-necessary identity (display, stats, persistence, tracing) |
| **`identity-scan`** | **DEFECT** — files as a failing-not-ignored test (when a divergence is constructible) or a FIXME naming the owner |

## 2. The register

### 2.1 CLOSED legs

**Backend — CLOSED (cited: `audits/cranelisp-backend-s110.md` §2.1, verified
grep-zero).** Four live `symbol_tables.iter()` sites, all enumerations, none
resolution:

| Site | Verdict | Grounds (audit §2.1) |
|---|---|---|
| `trace_codegen.rs:308` | enumeration | trace-descriptor discovery — completeness-by-construction over all entries (`tracing.md` §3.5); descriptor baking, no name input, no precedence |
| `utilization.rs:256` | non-identity | spark-stats call graph, env-gated reporting |
| `jit.rs:330` | enumeration | GOT data-symbol registration at `Jit::new`, one symbol per module KEY — order-insensitive by keying |
| `jit.rs:117` | enumeration — **tie-discipline convention-only; DECISION OWED (pre-seeded row)** | `register_platform_effect_symbols` registers by BARE name into the JIT's flat namespace, following `Import` edges; two same-named platform effects in different modules would be last-write-wins by DashMap order. Platform names are globally unique TODAY (convention, not structure). The sweep decides: structural tie-error (carve-out-1 discipline: "a tie is an ambiguity error, never broken by iteration order") vs a documented + asserted uniqueness invariant. `/qa` lean: the tie-error — convention-only uniqueness is exactly what the principle calls a scan-in-waiting; a `debug_assert`-on-collision is the minimum |

**Primitives / intrinsics / platform — CLOSED (this pass, 2026-07-17).**
`grep -rn 'symbol_tables\.iter()' crates/cranelisp-{primitives,intrinsics,platform}/src/`
→ **zero hits** in all three. No resolution role (they host tables and
bodies; they never resolve written names). Closed by the single grep pass the
sprint scope prescribed.

**`cranelisp-types/resolve.rs` — the sanctioned chain itself.** Not swept
(re-read only if a pattern hit lands there); the import/re-export follow, the
scope stack, and the prelude fallback are the keyed-lookup chain the
principle DEFINES as not-a-search.

### 2.2 OPEN legs (classified during S111; priority order per SPRINT §4)

**Leg 1 — `cranelisp-typecheck` (largest iteration surface).** Grep baseline
this pass: 0 × `symbol_tables.iter()`; 258 × class-2/3 hits to pre-filter by
acid-test part (a). Expected hot sites to reach the register: dispatch
candidate-set reads (keyed by Decision 0045 — should verdict `enumeration`
with type-match-computation grounds), `Overloaded` variant walks
(enumeration by definition), exhaustiveness ctor-set reads (enumeration),
any module-map walk inside resolution helpers (suspect). Register rows
appended below as classified.

**Leg 2 — `src/` (int).** Grep baseline this pass: **11 ×
`symbol_tables.iter()`** (+292 class-2/3 to pre-filter). Pre-listed for
classification, with provisional lean where the site's role is already
documented — every row still needs grounds verified before the verdict is
final:

| Site | Provisional lean | To verify |
|---|---|---|
| `src/worker.rs:1466` | ? | role of the walk — if it feeds resolution/dispatch it is suspect |
| `src/worker.rs:1567` | ? | same |
| `src/worker.rs:1586` | ? | same |
| `src/worker.rs:1602` | ? | same |
| `src/exe.rs:626` | enumeration? | `--link` emission walk — persistence/emission over the complete set; order must not affect link identity (Kahn's-sorted?) |
| `src/repl/search.rs:471` | search (carve-out 2) | the named sanctioned scan |
| `src/agent/harvest.rs:397` | non-identity? | `.any(\|t\| t.get(name).is_some())` — existence probe across ALL tables for harvest/agent context; D1-bounded IF the result never feeds resolution — verify no eval-path consumer |
| `src/session_v4/lifecycle.rs:910` | ? | classify — lifecycle sweep vs lookup |
| `src/session_v4/index_worker.rs:1109` | enumeration/search? | index feed — feeds the importable index (human-facing `/search` substrate), but verify no identity consumer |
| `src/session_v4/index_worker.rs:1994` | enumeration | key-set snapshot (`map(\|e\| e.key())`) — complete-set read |
| `src/session_v4/index_worker.rs:2014` | enumeration | same shape |

Int display/introspection paths are non-identity by D1 — but each display
site verdicted `non-identity` must be checked for an eval-path consumer
(the I-1 lesson: a "display" gate that eval also consults is resolution).

**Leg 3 — `cranelisp-frontend`.** Grep baseline: 0 × `symbol_tables.iter()`;
27 class-2/3 hits (small surface — reader/builder locals expected).
**Carried by `/audit`'s frontend rotation in depth** (post-quasiquote
landing, arch §7); its findings append here.

### 2.3 Findings protocol

- `identity-scan` verdict → failing-not-ignored test when a divergence is
  constructible (two candidates, incidental order flips the answer), else a
  FIXME naming the owner. Either way a row in `PLAN.md` §"Sprint 111" as a
  Phase-6 addendum.
- Contested verdicts → `/qa` arbitrates (attribution authority); recurrence
  of a scan CLASS in one bounded context → recommend an `/audit` rotation
  pull (trigger 6).
- The register's end-state at S111 close: every grep-class hit either
  verdicted here (with grounds) or pre-filtered `non-identity` by the part-(a)
  test; zero unclassified `symbol_tables.iter()` sites compiler-wide.
