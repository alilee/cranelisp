---
id: ACT-1065
title: The bind-chain pass identifies `bind` and platform functions by spelling
status: open
priority: blocking
from: qa
to: qa
sprint: 124
filed_at: 2026-11-17
refers_to:
  - spec/04-expressions.md
  - spec/08-modules.md
  - spec/10-io.md
  - src/bind_chain_analysis.rs
  - design/int/bind-chain-analysis.md
  - tests/plan/s124-evidence-delta.md
---

## Observation

Lead from `design`(int)
([bind-chain analysis §7](../../design/int/bind-chain-analysis.md#7-open-obligations)).
Executed by `qa` on `target/debug/cranelisp` at `4b58ab93`, 2026-11-17, in
scratch directories, no prelude. No leg imports the primitive `bind`.

**Silent wrong value.** Platform `poll-pool`, `--run`; `poll-read` returns
its last argument.

```clojure
(defn bind [io f] (primitives/bind io (fn [x] (f (add-i64 x 100)))))
(defn main []
  (bind (poll-read 1 1 3) (fn [a] (bind (poll-read 2 1 4) (fn [b] (Pure (add-i64 a b)))))))
```

| Leg | Program | Required | Observed |
|---|---|---|---|
| Subject | above | exit 207 | exit 7: the user's function never runs |
| Control | the function and both calls spelled `then` | exit 207 | exit 207 |
| Subject, dependent | the second read's last argument is `a` | exit 50 (the value 306) | refused: `undefined function: bind` |

**Legal program refused.** `(defn bind [a f] (f (add-i64 a 100)))`.

| Leg | `main` returns | Required | Observed |
|---|---|---|---|
| Subject | `(bind 5 (fn [x] (add-i64 x 1)))` | 106 | `codegen error …: undefined function: bind`, under `--run` and at the REPL |
| Subject, qualified | the function in module `m`, called as `(m/bind 5 (fn …))` | 106 | `undefined function: m/bind` |
| Control: the name | the function spelled `then` | 106 | 106 |
| Control: the shape | `(let [k (fn [x] (add-i64 x 1))] (bind 5 k))` | 106 | 106 |
| Control: the shape | a three-parameter `bind` called with an inline lambda | 106 | 106 |

**A local named like a platform function** (lead from `design`(int),
executed 2026-11-17). Platform `poll-pool`, `--run`, `poll-read` and the
primitives imported.

```clojure
(defn slow [t c d]
  (bind (poll-read t c d) (fn [x] (bind (poll-read t c d) (fn [y] (Pure (add-i64 x y)))))))
(defn go [poll-read]
  (bind (poll-read 1 1 150) (fn [a] (bind (poll-read 2 1 150)
    (fn [b] (Pure (sub-i64 (add-i64 a b) 600)))))))
(defn main [] (go slow))
```

| Leg | Program | Required | Observed |
|---|---|---|---|
| Subject | above | exit 0 | abort (134): `cranelisp_run_io: unknown IO tag 4` |
| Control | the parameter spelled `rd` | exit 0 | exit 0, serial (629 ms) |
| No face | a `let`-bound lambda named `poll-read` that returns `Pure` | 207 | 207, as its renamed twin |

**An imported user `bind` beside a prelude that exports the primitive**
(`arch`'s falsifier, T-1065-f). `m` defines the user `bind`, the entry
imports it by name, `prelude.cl` re-exports the primitive:
`undefined function: bind`. This face is not this defect's. It is
[ACT-1075](ACT-1075-polymorphic-candidate-selected-from-a-shared-spelling-is-undefined-at-codegen-intake.md),
which any spelling shows; the `then` control removed the second candidate
together with the spelling and could not tell the two apart.

## Classification: a defect

- **Requirement.** Spec §4.6: an application calls the function its callee
  resolves to. Spec §8.6.4 lets a module declare any unqualified spelling.
- **Class:** `routing-misclassify`. Faces: a silent wrong value, and a
  wrong reject.
- **Mechanism, confirmed by control.** `src/bind_chain_analysis.rs::is_bind_var`
  takes any callee spelled `bind`, or ending `/bind`, for the primitive.
  Each control differs from its subject in one of the three things the
  recogniser reads: the spelling, the inline lambda, the argument count.
  The pass's output was not dumped; the controls carry the attribution.
- **Refuted if** a renamed twin fails the same way, or a build that
  identifies the primitive by its resolved declaration still shows either
  face.
- **The platform face has the same cause in a second recogniser.**
  `src/bind_chain_analysis.rs::effect_descriptor` reads a scheduling class
  from the callee's spelling with no lexical layer. Its control differs
  only in the parameter's spelling. The abort is the panic the pass's
  leaf-only premise exists to prevent (evidence delta §4.1).
- **Relation to ACT-1050.** The designed reconstruction
  ([bind-chain analysis §3.6](../../design/int/bind-chain-analysis.md#36-reconstruction))
  is expected to remove the refusal. It does not remove the wrong value:
  grouping or launching a user's function changes the program.
- **Predicted, not observed.** Once row D3 accepts renamed imports, the
  primitive imported under another name is not recognised and its chain is
  never scheduled, against spec §10.12.1.

## Request

- `test` commits REPRO-1065
  ([evidence delta §3.8](../../tests/plan/s124-evidence-delta.md#38-repro-1065--the-bind-chain-pass-identifies-callees-by-spelling))
  in the S124 evidence wave.
- The correction is in S124's scope by the user's 2026-11-17 decision. It
  is designed in
  [bind-chain analysis §3.1](../../design/int/bind-chain-analysis.md#31-pattern-recognition)
  and lands in ACT-1050's change-set.
- Not allocated: the design's cycle-peer falsifier. Every import cycle is
  refused before a body is analysed (spec §8.10.2; observed for two
  shapes), so `design`(int) strikes that assertion or names a module-tier
  observation.

## Accepted at W4's exit (qa, 2026-11-18, `8667a868`)

- **Red to green.** The eight cells of REPRO-1065-a, b, c and e failed on
  their assertions at `f775478e` and pass at `8667a868` in `dev`'s full run
  and in `qa`'s focused run, with the seventeen controls. `dev`'s C8 module
  rows were RED before the change and pass.
- **T-1065-f stays RED and is re-traced to ACT-1075.** Its program fails
  the same way with the pass disabled and with spellings the pass never
  reads. The design's import assertion keeps `dev`'s module row
  `ambiguous_bind_is_not_the_primitive` as its evidence until ACT-1075's
  correction lets the cell execute.
- **Open:** T-1065-d, with row D3 in W7. This filing closes on it.

## Completion evidence

REPRO-1065-a to c and e fail as stated, then pass with their controls and
the C8 module rows (met, above); T-1065-d passes once row D3 lands.
