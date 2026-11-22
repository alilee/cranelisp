---
id: ACT-1112
title: Remove the `race` built-in once a library definition over `select` replaces it
status: open
priority: advisory
from: sprint
to: arch
sprint: 124
filed_at: 2026-11-22
refers_to:
  - design/arch/core-library-boundary.md §3 (C2)
  - spec/08-modules.md §8.8.3
  - src/bootstrap.rs::register_combinators
---

## Request

Carry the compiler consequence of the user's ruling of 2026-11-22 that `race`
is library, not language: it is `(select [a b])`, and spec §8.8.3 says a
construct a library can implement should belong to the library. Asked to
classify it as library in the specification now and carry the removal of the
built-in, the user answered "agreed carry". The specification states today's
built-in provision truthfully until the removal.

No failing test can carry this: `primitives/race` works. `arch` recorded the
change as consequence C2 — it crosses crates (the binary seeds the built-in,
the backend lowers it, the runtime may hold a body only it reaches) and the
standard library gains a one-line `race`. `arch` also recorded the limit of
its evidence: the equivalence with a two-branch `select` was observed for the
returned value only, not for tie order, a panicking branch or cancellation
timing.

## Completion evidence

- The equivalence measured for tie order, a panicking branch and
  cancellation timing, or the difference stated and ruled on by the user.
- The built-in removed under an approved public-API gate row, with `race`
  provided by the standard library and `timeout` unchanged in behaviour.
- The specification's interim statement of the built-in removed by `spec`.
