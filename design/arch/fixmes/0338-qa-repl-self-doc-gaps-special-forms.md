---
number: 0338
target: /qa
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: repl/spec.md §3.6 (/info MUST work) + §4.6 (bare special-form display) + line 702-715, src/bootstrap.rs (S81 0266 trace root metadata), src/session_v4.rs (/info //sig dispatch)
status: open
---

# REPL self-documentation gaps for special forms — bare `trace` missing `:Type` prefix + `/info`/`/sig` fail for all special forms

## Issue (Phase-6a /repl finding, S81)

Two self-documenting-REPL gaps surfaced when exercising the S81 root-`trace` form:

1. **Bare `trace` at the prompt omits the `:Type` prefix.** It prints
   `trace ; special form - Execution trace: …`, but every other special form shows the
   type-annotated form: bare `if` → `:(Fn [primitives/Bool a a] a) if ; special form - …`,
   `let`/`defn` likewise. The S81 0266 commit (`583c58b`) claimed to preserve the real
   `(Fn [a] Trace)` scheme at root, but the **bare display drops it**. Inconsistent with
   `repl/spec.md` §4.6 (lines 702-715) and the self-documenting-REPL Design Principle.

2. **`/info` and `/sig` return `unknown symbol` for ALL special forms** (`trace`, `defn`,
   `match`, `if`, …) — not just `trace`. `repl/spec.md` §3.6 requires `/info <name>` to
   display details; §3.5 `/sig` to show the type signature. Special forms are currently
   unreachable via `/info`/`/sig`. Pre-existing, but newly relevant now that S81 made `trace`
   a queryable root form — a user who learns `trace` is a root form will reasonably try
   `/info trace` and get an opaque "unknown symbol".

## Proposed resolution

Per the user-proxy defect protocol, **/qa authors narrow failing e2e tests** for both:
- bare `trace` self-doc MUST carry the `:Type` prefix like other special forms (`// spec:` →
  repl/spec.md §4.6);
- `/info <special-form>` / `/sig <special-form>` MUST resolve (`// spec:` → §3.6/§3.5),
  with a representative set (`trace`, `if`, `match`).
Then hand to **`/int`** (REPL display + introspection dispatch owner) for the fix. Both are
failing-not-ignored guards until resolved.

## Context

Phase-6a /repl assessment, S81. The `:Type` annotation reader-macro cases all produce correct,
non-opaque feedback (good demo material); these two special-form self-doc gaps are the
exceptions. Item 2 is pre-existing; item 1 is S81-deliverable polish. Cosmetic sibling (not
blocking): `:Foo 42` unknown-type error prints `(from module ``)` with an empty module name.
