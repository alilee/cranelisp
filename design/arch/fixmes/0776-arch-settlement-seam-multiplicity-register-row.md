---
number: 0776
target: /arch
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/typecheck/monomorphisation.md §11.8.10 (the three-window
  standing rule) + crates/cranelisp-typecheck/src/program/mono_collect.rs
  (`AutoCurryDrain`, the 6+1-seam auto-curry drain) — the recurring class
  question routed from the S115 W4 review
status: open
---

# Register row candidate: an operation run at N non-equivalent seams needs an enumerated seam taxonomy, not a per-seam judgement call

## Severity

**Important** (register-row candidate; no in-wave blocking effect).

## Issue — and the class /review believes is real

`/dev`(typecheck) proposed a standing rule from the S115 W4 work: *"every
deferral has a drain that discharges the SAME obligations as its inline twin"*,
claimed as the third instance of inline-vs-deferred asymmetry (0693, 0705, now
0719).

**`/review` judges the claimed instance count wrong but the underlying class
real, one level up.** Of the three cited:

- **0719 IS** inline-vs-deferred asymmetry — the deferred multi-sig dispatch arm
  omitted the callee retype its inline twin in `infer_apply` performs.
- **0693 is NOT** — it is name-vs-carrier re-derivation (P24), already
  generalized as "derive-and-fence" in the S115 instrumentation harvest
  (SPRINT.md Notes, prior 5).
- **0705 is NOT** — it is a consumer-totality gap over a closed variant family,
  already the coverage-by-variants class (prior 4).

So inline-vs-deferred has **one** clean instance, not three, and does not on its
own meet the 3rd-instance escalation bar.

The class that *does* meet it — with instances inside this one crate, this one
sprint — is broader:

> **An operation performed at N non-equivalent seams, where each seam's version
> can silently omit an obligation its siblings discharge.**

Instances:

1. **`pass4_monomorphise` — 3 settlement windows** (`monomorphisation.md`
   §11.8.10), already fenced by a standing rule with four hand-written
   idempotence obligations.
2. **The auto-curry drain — 6 seams + 1 deferred re-drain** (S115 W4), newly
   split into `AutoCurryDrain::{Deferrable, Final}` with the seam→discipline
   mapping carried in prose and the **non-deferring polarity as the default**
   (FIXME 0775).
3. **Inline vs deferred overload dispatch** (0719) — the deferred arm dropped
   the callee retype, and the fix had to be applied per-arm, one of which is
   still comment-only (FIXME 0774).
4. **§11.8.9's own scan discipline** ("name is a TRIGGER, carrier is the
   IDENTITY") was itself authored because the same collection ran at several
   collector sites with divergent keying.

Four instances, one crate. §11.8.10 already fences instance 1 by hand; nothing
generalizes the fence.

## The fourth-window question (answered, for the record)

`/sprint` asked whether the W4 deferred auto-curry drain constitutes a FOURTH
settlement window in the §11.8.10 sense. **`/review`'s independent answer: NO on
the letter, YES on the pattern.**

- **Letter — not breached.** §11.8.10's standing rule is scoped to
  `pass4_monomorphise` *invocations*. There are still exactly three
  (`finalize.rs:562`, `:717`, `:740`) — verified by grep. The W4 addition is a
  re-drain of `resolve_auto_curry` at `finalize.rs:607`, a *different pass*, and
  it sits at an already-existing point in the finalize sequence (immediately
  after `resolve_pending_overloads`), not at a newly-invented settlement point.
  `/dev`'s assertion is correct and the escalation did not need to fire in-wave.
- **Pattern — a new instance.** The rule exists because "harvest at N settlement
  points" is an architectural shape whose growth should be a deliberate event.
  W4 grew exactly that shape in a second pass, and did so with a *weaker*
  discipline than §11.8.10's (two enum values covering six non-equivalent seams,
  the mapping in prose, the dangerous polarity defaulted).

## Proposed resolution

`/arch` to consider a register row / principle refinement along the lines of:

> When one operation runs at more than one settlement seam, the seams are an
> **enumerated set with a named discipline per seam**, and the discipline is a
> **required** input at every call site — never a default, never prose. Growing
> the set is an architectural event.

That subsumes §11.8.10's hand-written standing rule as an instance rather than
leaving it as a one-pass special case, and it makes FIXME 0775 (`target: /dev`)
the mechanical consequence rather than a separate judgement call.

Note that this is the "coverage by definition variants" standing category
(MEMORY, S108) applied to *seams* rather than *definition forms* — the same
lever: the matrix that would have failed is `seam × obligation`, and its absence
is what lets each seam grow its own codepath.
