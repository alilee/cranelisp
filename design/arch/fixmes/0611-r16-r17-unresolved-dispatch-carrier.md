---
number: 0611
target: /arch
filed_by: /design (typecheck)
filed_at: 2026-07-15
sprint_filed: 110
refers_to: crates/cranelisp-typecheck/src/result.rs (CheckResult) + crates/cranelisp-typecheck/src/program/finalize.rs (unresolved-return-poly-dispatch set) → src/exe.rs::validate_main + the REPL __expr eval path (int)
status: open
---

# R16/R17 unresolved-return-poly-dispatch signal — ratify the typecheck→int carrier

## Context

R16/R17 (S110 scope §5; S109 W6.3 carry) is the return-type-poly ambiguity
error-quality defect: a bare `(zed)` (`zed : ∀a. Zeroable a => (Fn [] a)`) with
no context leaks `codegen error … __expr entry has no GOT slot` instead of the
clean §3.11 "add an annotation to pin the type" message. Dispatch itself WORKS
(rows 13–15 green — `:Int (zed)`, `(add-i64 (zed) 5)`); only the genuinely
UNRESOLVED case leaks.

The typecheck-side signal is designed in
`design/typecheck/return-poly-dispatch-signal.md`: at finalize, typecheck
collects the set of return-type-poly dispatch sites still UNRESOLVED after the
final substitution (grounded in the dispatch OUTCOME — `no impl selected` — not
in surface-type concreteness, which false-positived on `(add2 3 4)` in the S109
revert). Ordinary body value positions typecheck rejects directly. The one class
typecheck cannot reject itself is the **entry/eval RESULT position** (`main` for
`--run`/`--link`; `__expr` for REPL eval), because a poly-returning defn is a
legitimate deferred-polymorphic value except when an execution boundary demands a
concrete runnable value — and typecheck carries no entry designation (Principle
19). int must apply the signal at that boundary, so the signal must cross
typecheck → int.

## The decision requested

Ratify the carrier for the class-(b) entry/eval signal. `/design` (typecheck)
recommends **(A)**:

- **(A) — RECOMMENDED — a transient `CheckResult` field.**
  `CheckResult.unresolved_dispatch: Vec<UnresolvedDispatchSite>`, where
  `UnresolvedDispatchSite { span: Span, method: Symbol, gap: DispatchGap }` and
  `DispatchGap` enumerates the reason (return-directed-no-context; constraint-only
  value position; …). `CheckResult` is already declared "NOT a boundary type …
  diagnostics + optional REPL display payload" (`result.rs:14`), typecheck-owned,
  int-consumed — this is exactly a diagnostic payload. **No `cranelisp-types`
  edit, no `CACHE_SCHEMA_VERSION` bump** (the set is EMPTY for every valid
  program — an unresolved dispatch surviving to finalize is the error we reject —
  so there is nothing to serialize into the cache). typecheck stays the sole
  deriver (Principle 24); int reads a decision at `validate_main` + the `__expr`
  eval path, never re-running dispatch. Cost: a typecheck `public-api.txt` field
  add (baseline regen).

- **(B) — a serde'd `MethodResolutions` sidecar** (`HashMap<Span, …>`, mirroring
  `pattern_ctors`). Not recommended: `MethodResolutions` is cached; caching an
  always-empty-for-valid-programs error-path map is a schema bump for no value.

- **(C) — a new `CranelispError`/`CheckError` variant + int re-derivation.** Not
  recommended: int would re-inspect the entry result's dispatch state, re-deriving
  the discriminator typecheck already holds (Principle 24 violation) and
  re-importing the `(add2 3 4)` false-positive risk into int.

**Specific point for `/arch`:** under (A) the carrier needs **no types-level
type** — `UnresolvedDispatchSite`/`DispatchGap` are typecheck-owned and int
already depends on typecheck. Confirm they stay typecheck-local, OR rule them
into `cranelisp-types` if a future non-int consumer is anticipated (e.g. a
backend defence-in-depth arm that, on reaching a slot-less dispatch result, emits
the clean §3.11 message rather than the GOT-slot leak — a belt-and-braces sibling
to the typecheck gate). The Phase-2 Rev-4 note flagged this "may need a
types-level carrier (error variant or `CheckResult` field)"; (A) resolves it as a
`CheckResult` field with no types edit.

## Coordination

This is one coordinated typecheck+int change-set (S110 scope §5 / Phase-2 impact
table R16/R17 row). Wave ordering: after 0583-W0 and 0590 on the typecheck serial
chain (Phase-2 §8). The int half (`src/exe.rs::validate_main` entry-ambiguity +
the `__expr` eval-path consult) is `/design` (int) + `/dev` (int); this FIXME
gates the shared carrier shape so it is budgeted, not discovered mid-wave.
