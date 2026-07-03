---
number: 0492
target: /repl
filed_by: /docs
filed_at: 2026-07-03
sprint_filed: 101
refers_to: repl/spec.md §18.4 ("`/sig` on a broken symbol MUST show the same primary line and provenance comment line as bare lookup"), §3.1 (/sig row), §1.4 (fully-qualified type display)
status: open
---

# `/sig` primary line is not fully qualified — diverges from §18.4's "same primary line as bare lookup"

## Issue

`/sig <name>` renders the primary line with **unqualified** type names and an
**unqualified** symbol name, while bare lookup of the same symbol renders both
fully qualified. `repl/spec.md §18.4` says `/sig` on a broken symbol MUST show
the *same primary line* as bare lookup; as built the two differ (observed on
both broken and healthy symbols, so this is `/sig`'s general rendering, not a
broken-path special case).

## Repro (verified 2026-07-03 on `target/debug/cranelisp`, fresh dir, no prelude)

Same-session, same symbol (broken `k` from the §18.3 worked shape):

```
user> /sig k
:(Fn [Int] Int) k ; defn
; broken by the redefinition of user/f: type error at 12..29: type mismatch: expected primitives/String, got primitives/Int

user> k
:(Fn [primitives/Int] primitives/Int) user/k ; defn
; broken by the redefinition of user/f: type error at 12..29: type mismatch: expected primitives/String, got primitives/Int
```

Healthy symbol, same divergence: `/sig k` → `:(Fn [String] Int) k ; defn`
where bare lookup shows `:(Fn [primitives/String] primitives/Int) user/k`.
(The provenance comment line DOES match — only the primary line differs.)

The existing pin `tests/repl_introspection.rs::sig_shows_type_signature`
asserts only that the output contains `Fn`, so the divergence is untested;
`tests/repl_redefinition.rs::redefine_broken_caller_info_and_sig_report_broken_status`
pins the provenance line, not the primary line.

## Proposed resolution

`/repl` arbitrates the intended display: either (a) `/sig` is meant to match
bare lookup exactly — then feed `/qa` a narrow failing test and route the fix
to `/int` (`repl.rs` display seam), or (b) `/sig` intentionally renders the
short form — then amend §18.4's "same primary line" wording (and §3.1 if
needed) so spec and binary agree.

## Operational implication / Context

Surfaced while verifying transcripts for `user/guide/live-development.md`
(S101 Phase 6b). The guide prints `/sig` output as built (short form), so no
doc change is owed either way; whichever way the ruling goes, the guide's
transcript stays faithful until the binary changes.

## /qa note (S101 6b guard batch, 2026-07-03): guard landed against CURRENT §18.4 text

`tests/repl_redefinition.rs::sig_broken_symbol_primary_line_matches_bare_lookup_fully_qualified`
(RED) asserts the FQ primary line from /sig per §18.4's "same primary line"
MUST as written. If this FIXME's arbitration amends §18.4/§3.1 to pin the
short form instead (option b), the guard's expected values re-anchor — the
test carries a NOTE to that effect. Ledger: `tests/plan/ledger.md` §"Sprint
101 Phase 6a/6b defect set".
