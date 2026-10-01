---
id: ACT-1035
title: In the REPL, calling a concrete impl's method crashes the session after a parametric impl of the same trait is defined later
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - repl/spec/05-error-presentation.md §5.1
  - spec/07-traits.md §7.3.3
  - tests/spec_07_traits.rs
  - tests/plan/s122-evidence-delta.md
---

## Observation

QA found this on 2026-09-30 while attributing
[ACT-1034](ACT-1034-parametric-impl-instance-body-polymorphic-callee-intake.md).
It used `target/debug/cranelisp` built after `88bbbd12` and the
`primitives-only.cl` fixture prelude. Each session started in a fresh
directory, with no `user.cl`.

```clojure
(deftype (Opt a) Nope (Yep [:a v]))
(deftrait Size (size [self] Int))
(impl Size Int (defn size [n] n))
(impl Size (Opt a) (defn size [o] 1))
(size 5)
```

- **Deterministic:** the REPL process dies with SIGSEGV (exit -11) in 10 of
  10 sessions, with no error line.
- **Violation:** REPL §5.1 requires that errors not crash the session.
- **Mode divergence:** `--run` of the same program exits 5.
- **Not an S122 regression:** it also crashes a release binary built on
  2026-09-29 at 09:31, before `e4062202`.

| Control (REPL, fresh session) | Result |
|---|---|
| Constrained `(Opt :Size a)` impl in place of `(Opt a)` | crashes |
| A `Bool` impl, then `(size true)` | crashes |
| Parametric impl defined *before* `impl Size Int` | `:primitives/Int 5` |
| Monomorphic `(impl Size (Opt Int) …)` in place of the parametric impl | `:primitives/Int 5` |
| No second impl | `:primitives/Int 5` |
| `(size (Yep 41))` with the parametric impl declared first | `:primitives/Int 42` |

The crash makes the depth-1 case of the §7.3.3 canonical example crash too,
when the scalar impl is entered first.

## Attribution

- **Status: provisional.** The trigger is isolated. No seam observation
  explains it.
- **Trigger:** a *parametric* impl of trait `T` defined after a concrete impl
  of `T`, followed by a call that dispatches to the concrete impl.
- **Seam observation.** The CLIF of the crashing call is shaped like the
  passing `--run` CLIF. It calls through the GOT table.
  `CRANELISP_GOT_TRACE=1` printed nothing on this path.
- **Hypothesis:** registering the later parametric impl leaves the concrete
  instance's dispatch slot invalid, perhaps by re-emitting or re-keying it.
  The owner would then be `src/` REPL session integration. The candidate
  class is `null-got-slot`.
- **Refuted if** the concrete instance's slot holds valid code at the crash.
  One way to check is a slot dump taken before the call.

## Evidence allocation

- **`test` (allocated now):** commit the five-line program as a failing,
  un-ignored REPL cell.
  - Cite `// spec: repl/spec/05-error-presentation.md §5.1`.
  - Use a provisional `class=mode-divergence`, to be re-classed at
    attribution.
  - Assert that the session survives and prints `:primitives/Int 5`.
  - Add two passing controls: the parametric-first ordering in the REPL, and
    the same program under `--run`.
- **`dev`:** the unit row at the seam the attribution names, landing with the
  fix.
- **Coverage attribution:** no REPL cell enters a parametric impl after a
  concrete impl of the same trait and then calls the concrete one. Every
  existing constrained-impl cell defines a single impl.

## Disposition

- This is a deterministic crash of an ordinary REPL program.
- Fix or carry is the user's decision under METHOD §2.4.
- QA retains this intake.

## Completion evidence

The cell goes RED (the session dies), then GREEN after the correction, with
both controls still passing. `test` then adds the REPL leg to ACT-1034's C1
control, `parametric_impl_instance_calls_monomorphic_target_batch_control`,
which this crash blocks today.
