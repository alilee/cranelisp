---
id: ACT-1105
title: A qualified `primitives/Bind` constructs an IO node one word shorter than the runtime reads, where the bare spelling is refused
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-22
refers_to:
  - spec/10-io.md §10.1
  - design/backend/io-trampoline.md §1.3
  - design/arch/core-library-boundary.md §2
  - src/bootstrap.rs
  - crates/cranelisp-intrinsics/src/io.rs::read_bind_transition
  - crates/cranelisp-backend/src/compiler/io_nodes.rs::emit_bind_node
  - crates/cranelisp-typecheck/src/checker.rs::is_internal_constructor_check_with_state
---

## Origin

`sprint`, reading source for a user question, with `arch`'s observation in
[core/library boundary §2](../../design/arch/core-library-boundary.md) that
`(defn mybind [io f] (primitives/Bind io f))` compiles and sequences. `qa`
took it in on 2026-11-22.

**Whether the constructor is language surface is open with the user. This
filing does not settle it.** It records what happens today.

## What compiles

`qa`, 2026-11-22, the debug binary built from `11ea995e` (no compiler source
has changed since), no prelude, `--run --no-cache`, a scratch directory
since removed. Each program imports `Pure`, `Int` and `add-i64` from
`primitives`; `K` is `(fn [x] (Pure (add-i64 x 41)))`.

| Program | Observed |
|---|---|
| `(defn mybind [io f] (primitives/Bind io f))`, `(mybind (Pure 1) K)` | **Exit 42** |
| `(primitives/Bind (Pure 1) K)` as `main`'s body | **Exit 42.** At the REPL, 42 too |
| `(primitives/IO.Bind io f)` in `mybind` | **Exit 42** |
| `(let [b primitives/Bind] (b (Pure 1) K))` | **Exit 42** |
| `(import [primitives [Bind]])`, then `(Bind io f)` | Refused: `cannot construct internal type constructor 'Bind'` |
| A `match` arm `(Bind a b)`, with the import | Refused: `cannot match on internal type constructor 'Bind'` |
| A `match` arm `(primitives/Bind a b)` | Refused at codegen: `constructor 'primitives/IO.Bind' is matched at an instantiation that is not concrete (Var(8))` |
| Control: the builtin `(bind (Pure 1) K)` | Exit 42 |

## What the node holds

From the emitted code (`CRANELISP_CODEGEN_DUMP`), one program holding both:

| Producer | Allocation payload | Words stored |
|---|---|---|
| The constructor `primitives/IO.Bind` | 24 bytes | the tag at 16, `inner` at 24, `cont` at 32. **Nothing at 40** |
| The builtin `bind` | 32 bytes | the tag, `inner`, `cont`, and the input disposer at 40 (zero for an `Int`) |

With the 16-byte header the constructor's block is 40 bytes, so offset 40
is the first byte past it.

## What the runtime does with it

Read in source:

- `read_bind_transition` reads the word at offset 40 of every node tagged
  as a bind, as the input disposer. **For a constructor-built node that
  read is past the end of the allocation.**
- The word is carried with the continuation. It is **not used** when a
  produced value reaches its continuation, which is the ordinary path.
- It is **called as a function, if it is not zero,** when a produced value
  is dropped before reaching its continuation. The one such drop `qa`
  found is in a blocking branch run on a worker under a cancellation
  lease.

Observed, with `CRANELISP_RC_STATS` and lenient evaluation off:

| `main`, through `mybind` and through the builtin | Constructor | Builtin |
|---|---|---|
| A scalar intermediate, the first row above | 42; 4 allocations, 4 frees | 42; 4, 4 |
| `(Pure (str-concat "ab" "cd"))` then `(fn [s] (Pure (str-len s)))` | 4; 7, 7 | 4; 7, 7 |
| The same intermediate, unused by the continuation | 7; 7, 7 | 7; 7, 7 |
| Two nested, both with a `String` intermediate | 6; 12, 12 | not run |
| The loser of a `race`: a blocking sleep of 300 ms under the bind, against one of 30 ms | 7, in 3 of 3 runs | 7 |

- **On the ordinary path a constructor-built node behaves as the builtin
  does,** with an intermediate value that owns heap memory included: same
  value, same balance.
- **`qa` did not reach the call of the stray word** from a program. The
  race above did not show it. Which user program makes the runtime drop a
  value under a constructor-built node is not established.
- **`qa` did not observe the stray word's value.** This environment has no
  memory checker or debugger.

## Classification: a defect under either answer to the open question

- **Against the specification as written it is already a defect.**
  [Spec §10.1](../../spec/10-io.md) says `Bind` "cannot be constructed or
  pattern-matched by user code". The committed cells
  `spec_10_io::bind_constructor_rejected` and `bind_pattern_rejected` use
  the bare name only.

- **If the constructor is not language surface,** the qualified, dotted
  and value spellings construct it where the bare spelling is refused: one
  constructor, two outcomes by spelling. The qualified match is refused by
  the wrong stage with an internal key.
- **If it is language surface,** the node it builds is one word shorter
  than the layout the runtime reads
  ([IO trampoline §1.3](../../design/backend/io-trampoline.md)), and the
  bare spelling is refused where it should construct.
- **Severity: memory-unsafe, latent.** Every forced constructor-built node
  is read past its allocation. No wrong value, leak or crash was observed.
  The harmful use, a call through the stray word, is read in source and
  was not reached.
- **It predates S124.** The two-field seed dates from S76 (`d62db121`); the
  third word from S121 to S122 (`992cb595`, `7f834bf6`).

## Attribution

Two sites, each with its own control.

- **The short node: `src/bootstrap.rs`.** It seeds the constructor's body
  as a two-field construction at tag 2. The backend's `emit_bind_node`
  writes three. Control: the two rows of the emitted-code table, in one
  program. **Refuted if** the constructor's emitted code stores a word at
  offset 40.
- **The spelling: typecheck's internal-constructor gate.** The bare name is
  refused and the qualified name is not, with nothing else changed. `qa`
  did not read why the gate, which resolves the name it is given, lets the
  qualified spelling through. Provisional as to the line.
- **The reader is as designed.** The trampoline reads a three-word node
  because the design says only the builtin creates one.

## Routing

- **`qa` holds this action.**
- **`test`:** T-BIND-SPELLING, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`arch`, then `design`(typecheck) and `design`(int):** the correction
  follows the user's answer. Either the gate refuses every spelling, or the
  seeded constructor builds the node the runtime reads.
- **`dev`, with the correction:** a module row at whichever site is kept.
  No solution-level cell can show the short node: the ordinary path is
  identical.

## Completion evidence

T-BIND-SPELLING is committed and observed RED. The user's answer is
recorded by `spec`; `qa` then narrows the cell to it. The module row passes
and was seen to fail first.

## Narrowed after the ruling on `IO` (qa, 2026-11-22)

The user ruled `IO` opaque: no spelling may construct `Bind`. T-BIND-SPELLING
is accepted as committed (`e9a60317`): the bare spelling is refused and the
other three are not, so its agreement clause fails. It is narrowed to
refusal of all four in T-IO-OPAQUE (evidence delta §14.3). Carried to the
next sprint by the user's decision.
