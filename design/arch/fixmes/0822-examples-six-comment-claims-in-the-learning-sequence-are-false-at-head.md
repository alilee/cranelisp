---
number: 0822
target: /examples
filed_by: /examples
filed_at: 2026-07-21
sprint_filed: 115
refers_to: examples/07-polymorphism.cl:8-10; examples/10-adts.cl:24-25;
  examples/14-vecs.cl:80-86; examples/32-concurrency-combinators.cl:118-119;
  examples/Cranelisp.toml:11-12; examples/{01,02,06,08,09,10}-*.cl +
  examples/lib/prelude.cl (ring framing); examples/plan-examples.md §2c.3
status: open
---

# Six comment-claims in the learning sequence are false at HEAD — the corpus teaches boundaries only in prose, and the prose has rotted

## Why this is filed as a FIXME at all

Self-targeted, deliberately: `/examples` files it so the **wave gate sees it**
(`/sprint` scans `design/arch/fixmes/` for `target: /skill-in-wave` +
`status: open`) and so the fixes cannot quietly slip past the S115 6b
change-set. It closes in 6b. It is a **documentation** defect set, not a
compiler defect set — no example fails, in either mode — so no `/testing` repro
is owed under root `CLAUDE.md` §"Usability Findings and Defects".

## Severity

**Moderate.** Nothing breaks. But an example is prose that happens to compile,
and a reader has no way to check prose. Two of the six actively steer a reader
toward something that does not work (the vec one toward a shape that SIGBUSes),
and one teaches behaviour the spec explicitly rejected.

## The six

1. **`07-polymorphism.cl:8-10`** — *"In batch mode, each polymorphic function is
   used at one concrete type per program."* **False.** Probe (free-standing,
   `cwd=examples/`): `(defn id [x] x)` used at both `Int` and `Bool` in one batch
   `main` compiles and exits 5. The example *named* polymorphism states the
   opposite of let-polymorphism and never demonstrates multi-instantiation.
2. **`10-adts.cl:24-25`** — *"Field access requires pattern matching (next
   example)."* **False** since §5.2.6 generated accessors. Probe:
   `(Point.x (Point 3 4))` → 3. This one has corpus-wide reach: every example
   reads a single field with a full `match`, which is no longer the idiomatic
   form (see `plan-examples.md` §2c.1 A2).
3. **`14-vecs.cl:80-86`** — *"The same generic higher-order function can be
   instantiated at several different vec primitives — e.g. `call-get` works
   whether you hand it `vec-get`, `vec-set`, or any function of the matching
   shape."* **That shape SIGBUSes** (open defect FIXME 0483). The code directly
   below the comment carefully uses three separate one-op helpers to avoid it,
   and `plan-examples.md` §"Notes on specific entries" records the avoidance as
   a deliberate constraint. The comment invites the crash the code dodges.
4. **`32-concurrency-combinators.cl:118-119`** — *"the empty `select []` never
   completes"*. **Contradicts spec §10.12.8 at HEAD**, which pins a **fatal,
   non-catchable runtime raise** and says in terms that a hang is
   *non-conforming*: "a guaranteed deadlock is worse than a clean fault". The
   example teaches the resolution the `/spec` ruling (S98, FIXME 0487) rejected.
5. **`Cranelisp.toml:11-12`** — *"lib-dirs fully replaces the env and default
   tiers when present, so this config isolates examples from
   `{project_root}/stdlib/`."* **Contradicts §8.11.4** (settled S91): the
   lib-directory set is an **additive UNION**; no source replaces or suppresses
   another. The isolation *guarantee* still holds — but because the project root
   is `examples/` and `examples/stdlib/` does not exist, not because the toml
   overrides anything. Worth correcting precisely, because the union semantics
   are also the explanation for the standing operational rule that **setting
   `CRANELISP_LIB` breaks free-standing example runs**: it *adds* the real
   stdlib to the set rather than being overridden.
6. **Ring framing** — `01`, `02`, `06`, `08`, `09`, `10` and `lib/prelude.cl`
   still describe primitives as *"Ring 0"/"Ring 1"*. The ring axis was retired
   as a project-wide scheduling axis in **Sprint 64**; `plan-examples.md` §2's
   own preamble declares it removed. It was removed from the plan, not from the
   examples a reader actually reads.

## Root cause, and the part worth acting on beyond the six

The sequence teaches every compile-time boundary as a **comment**, because a
runnable example cannot type-error. Comments are inert: nothing verifies them,
nothing regresses when they go stale, and six of them went stale without a
single test going red.

The structural remedy is in `examples/plan-examples.md` §2c.1 A1 and §2c.3:
the **runtime** half of the negative space *can* be made runnable and
exit-code-guarded via `catch-runtime-error` (verified free-standing at 6a:
div-by-zero and vec-out-of-bounds both catchable, exit 2). Landing that converts
a class of rotting prose into regression-guarded teaching. The compile-time half
stays prose and needs a re-verification pass each sprint — which is what the
standing assessment in §2c now exists to force.

## Disposition

Items 1-6 land as correction beats 5-9 in the S115 Phase-6b change-set
(`plan-examples.md` §2c.6). Item 2's full corpus-wide accessor conversion is
S116 work (§2c.5); 6b only removes the false sentence and points forward.
Item 3 does **not** close FIXME 0483 — the comment fix removes the invitation,
the defect stands.
