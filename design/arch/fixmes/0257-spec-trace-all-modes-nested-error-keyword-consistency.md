---
number: 0257
target: /spec
filed_by: /arch
filed_at: 2026-06-04
sprint_filed: 76
refers_to: spec/02-grammar.md §2 (reserved words), spec/04-expressions.md §4.12.3 §4.12.4 §4.12.5 §4.12.9, spec/03-types.md §3.2.4, spec/11-stdlib.md §11.1, appendix-a-builtins.md, design/arch/tracing.md §2.2 §2.4 §2.5 §3.1 §3.5.1 §6
status: open
---

# Trace spec: all-modes availability (retract §4.12.9 link rejection), nested-trace-is-an-error (§4.12.5), what-is-traced widening (§4.12.3), and the ROOT-special-form + reserved-name consistency fix (§2 / §3.2.4 / §4.12.4 / §11.1 / appendix-A)

## Issue

The 2026-06-04 user ruling changes four trace behaviours the spec currently states differently. `/arch`
records the target in `design/arch/tracing.md`; the normative spec text is `/spec`'s to author. Proposed
wording below.

## Proposed resolution

**1. §4.12.9 Build-Mode Restriction — REPLACE with all-modes availability.** `(trace ...)` now works in
ALL modes including `--link` (user: "happy to let tracing applications be linked"). The trace runtime is
an ordinary intrinsic force-linked into the standalone staticlib. Proposed replacement:

> ### 4.12.9 Build-Mode Availability
> `(trace ...)` is available in all build modes — REPL, `--run`, and `--link` standalone binaries. The
> trace runtime is part of the language's runtime support and is present in every produced artefact. A
> `(trace ...)` form behaves identically across modes (the rules of §4.12.1–§4.12.8 apply unmodified).

(Delete the old product-shape rationale paragraph; trace is no longer dev-only.)

**2. §4.12.5 Nested Trace — REPLACE "outermost wins" with "nested is a runtime error".** Same-thread
re-entrant trace is now disallowed via a runtime guard. Proposed replacement:

> ### 4.12.5 Nested Trace
> A `(trace ...)` expression MUST NOT be evaluated while another `(trace ...)` is actively tracing on
> the same thread. An implementation MUST raise a runtime error when a `(trace ...)` form is entered
> during the evaluation of an enclosing `(trace ...)` body — whether the inner form appears lexically
> (`(trace (trace expr))`) or is reached dynamically through a function call. Concurrent tracing on
> different threads is governed by §4.12.6 (at most one thread traces; others return an empty trace).

**3. §4.12.3 What Is Traced — WIDEN.** Discovery now swaps ALL symbol tables (stdlib + extern primitives
included). Update the "NOT instrumented" list: **remove** "Library modules" and "Extern primitives" and
"Compiler-seeded synthetic module functions" from the exclusion list — they ARE now traced (any callable
with a GOT slot). **Keep** "Inline primitives" (no callable entry — structurally untraceable) and
"Anonymous lambdas" (no named GOT entry) in the exclusion list. Also drop the "whose source file is under
the project root" qualifier from the instrumented-set definition (the project-root filter is deleted).
Confirm with /arch if the spec wants to keep the door open to a future opt-in narrowing — `/arch`'s read
is no (completeness-by-construction is the design; the dynamic-call hole disqualifies narrowing —
`tracing.md` §3.5).

**4. `trace` is a ROOT special form, RESERVED — terminology + reserved-list fix across §4.12.4 /
appendix-A / §11.1 / §3.2.4, plus a NEW §2 grammar entry (user ruling 2026-06-04).** The user ruled
afresh: `trace` is a **root special form** — treated specially by the parser/AST-builder and the
typechecker (the dedicated `Expr::Trace` node + `infer_trace` dispatch, the same recognition family as
`defn`/`let`/`if`/`match`), **always available, no import, no module path** (there is NO
`primitives/trace`), and its name is **RESERVED** (users cannot define or bind it). This SUPERSEDES the
prior pass's "parser keyword exception" framing and resolves the keyword-vs-module-scoped question
definitively (it is root-scoped). The spec-staleness determination FLIPS from the prior pass:
§4.12.4 / appendix-A's "always available" SUBSTANCE is right (terminology should align to "special
form, root-scoped"); §11.1's import-requirement is stale **for the form** but **stays for the ADT**.

   **(4a) §11.1 — fix the form/ADT conflation.** §11.1 currently says "Module-scoped special forms
   (`trace`) require import from their defining module" — stale **for the form**. Proposed:

   > - **Special forms**: The structural special forms (`defn`, `deftype`, …) and `trace` are all
   >   **root special forms** — parser keywords with distinct syntax, always available without import
   >   and with no module path. `trace` produces a distinct trace node; the `Trace` / `TraceCall` types
   >   and the field accessors it returns ARE `primitives`-module entries that DO require import — the
   >   deliberate form/ADT asymmetry, mirroring `Sexp`-in-`macros` (see §3.2.4).

   **(4b) §4.12.4 + appendix-A — terminology alignment.** Where these say `trace` is "always available"
   keep the substance; align the *terminology* to "root special form (always available, no import, no
   module path), reserved name." appendix-A's `trace` entry should classify it as a root special form,
   not a module-scoped name.

   **(4c) §3.2.4 — state the form/ADT asymmetry explicitly.** §3.2.4 already puts the import requirement
   on the *names* (correct). Confirm it states the asymmetry in terms — the keyword needs no import; the
   `Trace`/`TraceCall`/accessor names do — and cross-references the `Sexp`-in-`macros` precedent.

   **(4d) §2 grammar — NEW reserved-word entry + binding-rejection statement.** `trace` joins the
   reserved-word list in the grammar (alongside the other root special-form names). Add the normative
   binding-rejection statement: **a program MUST NOT define or bind the name `trace`** — `(defn trace
   …)`, `(let [trace …] …)`, `(fn [trace] …)`, and any other binder/definition position naming `trace`
   are rejected (not allowed-but-shadowed). User-accepted cost. (Enforcement owner is `/dev (frontend)`,
   FIXME 0259 — the AST builder's binder/definition paths gain the reserved-name reject; the as-built
   compiler does NOT currently enforce this.)

## Operational implication / Context

These are spec-text changes; the implementing /dev FIXMEs are 0254 (intrinsics), 0255 (backend), 0256
(int), and **0259** (frontend — reserved-name enforcement, the implementation owner for item 4d's
binding-rejection rule). Update the `[Tested ...]` annotations on the affected spec rows where the
existing trace tests' expectations change (coordinate with /qa FIXME 0258 — `trace_nested_single_trace`
becomes a nested-error test; the "what is traced" tests gain stdlib/primitive expectations; a new test
asserts `(defn trace …)` / `(let [trace …] …)` is rejected — pair with 0259). Sequencing is **/sprint +
user's call** — the spec text can land alongside or just before the /dev waves.
