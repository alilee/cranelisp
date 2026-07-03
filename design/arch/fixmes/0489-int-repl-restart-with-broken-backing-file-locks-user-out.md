---
number: 0489
target: /int
filed_by: /repl
filed_at: 2026-07-03
sprint_filed: 101
refers_to: repl/spec.md §18.8 (restart MUST reach a prompt), repl/spec.md §14.4/§14.6, design/int/session-transaction.md §10 T1
status: open
---

# REPL restart with a broken backing file exits(1) — user is locked out of the in-REPL repair path

## Issue

S101's redefinition machinery makes a non-compiling backing file reachable purely from
in-REPL actions: break a symbol via a signature-changing redefinition (ordinary,
recoverable session state per §18.4), quit, restart. As-built the restart prints the load
error and **exits with code 1 before the first prompt** — the user never reaches a prompt,
so the §18.6 repair path (redefine either symbol) is unavailable and the only recovery is
hand-editing `user.cl`.

Repro (S101, `target/debug/cranelisp`, `CRANELISP_LIB=stdlib`):

```
; session 1
(defn f [x] (+ x 1))
(defn k [x] (f (* x 2)))
(defn f [s] (primitives/str-len s))   ; k breaks — expected, reported
/quit
; session 2, same directory
→ user.cl:1:1: error: module error at 0..0: module 'user' failed: type error at 49..60: ...
→ exit code 1, no prompt
```

Two further problems with the error line itself (also the §18.8-floor "naming the broken
symbol" MUST): the broken symbol `k` is never named — only a span into `user.cl` — and the
`user.cl:1:1` prefix disagrees with the `at 49..60` span, plus the `module error at 0..0`
wrapper is internal noise.

## Proposed resolution

Per the new `repl/spec.md` §18.8 bullet ("The restart MUST reach a prompt", tagged
[S102]): on entry-module restore failure, start the session anyway, display the load
error (§5.1 format, naming the broken symbol), and enter the §14.4 error-blocked state
for the failing module — slash commands available, evaluation refused with the §14.4
message, error cleared when a definition turn or external file fix makes the module
compile. A definition turn at the prompt MUST be accepted while the entry module is
error-blocked (it is the repair).

## Operational implication / Context

Until fixed, any user who ends a session with a broken symbol loses REPL access to that
project directory. This directly undercuts §18.4's "broken-ness is ordinary, recoverable
session state" and the sprint's headline UX. /qa: the repro above is two short piped
sessions in one directory — suitable for a narrow e2e (assert session 2 reaches a prompt
and can repair via redefinition).

## /qa guard batch (S101 6b, 2026-07-03): guard LANDED

RED guard in `tests/repl_persist_redefine.rs`
(`restart_with_broken_backing_file_reaches_prompt_and_accepts_repair`) —
two-session e2e asserting the §18.8 [S102] floor: session 2 reaches a
prompt and accepts the redefinition repair (`:primitives/Int 4`). RED-first
verified (exit 1 before the prompt). The failing test is the trigger;
/int deletes this file with the fix.
