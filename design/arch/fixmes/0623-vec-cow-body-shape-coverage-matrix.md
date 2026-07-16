---
number: 0623
target: /qa
filed_by: /arch
filed_at: 2026-07-16
sprint_filed: 110
refers_to: tests/vec_assoc_param_mutate_return_uaf.rs + tests/vec_cow_value_use_leak.rs + design/arch/ownership-inference.md §3.7
status: open
---

# vec-COW coverage: body-shape × branch × face matrix + two new fences

## Context

The S110 W2 review (R-W2-1) found the vec-assoc UAF matrix (VA-1..4) covered
faces and value-use shapes but had **no body-shape variant axis**: the direct
body `(defn f [v i x] (vec-set v i x))` was fixed and pinned, while the
2-line let-wrapped and match-arm siblings still UAF'd — the classic
definition-variant coverage miss (the standing "coverage by definition
variants" audit category). `/arch` ruled the class fix
(`design/arch/ownership-inference.md` §3.7 — `ResultMode::MayAliasOf` +
truthful COW declarations + declared-fact reachability), carried to S111 with
the `/testing` sibling repros as the failing-not-ignored trigger.

## The ask

1. **Body-shape × branch × face matrix** for COW-in-return-position:
   {direct body, let-wrapped, match-arm, if-branch, chained COW} ×
   {in-place (rc==1 source), shared (rc>1 source → copy branch)} ×
   {REPL, `--run`, `--link`}. Positive = correct value + clean exit;
   negative = no premature free (RC-trace balanced), no SIGABRT. The W2
   review's probe list (chained `(vec-push (vec-push v 4) 5)`, lambda-captured
   source, nested double-COW) names the cells already probed SAFE — pin the
   load-bearing ones rather than re-probing all.
2. **Return-position copy-arm leak fence** (extends the VA-4 /
   `vec_cow_value_use_leak` family): after the S111 fix, a shared-source COW
   returned through a NON-direct shape conservatively over-incs the copy arm
   by one (retain-side residual, §3.7 — cured only by the later per-site-fact
   generalization). The fence should PIN the residual's magnitude (exactly
   one count per call, never a UAF) so an accidental widening is visible, and
   flip when the exactness generalization lands.
3. **Declared-fact reachability fence**: a prelude-fallback module exercising
   a `Borrowed`-declared primitive (e.g. `str-eq`/`vec-len` in a loop) must
   show the narrowed emission once §3.7(a3) lands — the fence that would have
   caught the "declared facts silently dead in production" gap this class hid
   behind.

## Closure

`/qa` actions into `tests/plan/` (matrix + fence rows, `/testing` dispatch
rows for S111) and deletes this file.
