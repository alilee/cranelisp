# Examples Plan — Learning Sequence Design

`training` owns this plan: what each example teaches, the rules the sequence
follows, and the open gaps between the sequence and the language. The files on
disk are the sequence of record. `tests/examples.rs` (owned by `test`) pins
their exits. [`AGENTS.md`](AGENTS.md) holds the operating rules and the
verification gate. [`lib/README.md`](lib/README.md) holds the library rules.
Where this plan and `spec/` disagree, the spec governs and this plan is repaired.

A dated observation is evidence of that date. Undated statements describe the
current tree.

## 1. Design principles

1. **One new capability per example**, in the simplest program that makes it
   clear.
2. **Cumulative.** An example uses only what earlier examples taught, plus
   library modules whose earning lesson precedes it.
3. **Comments explain the capability**, not the syntax. The code and its
   results teach the syntax.
4. **Boundaries are taught, not only happy paths.** Where a boundary can run,
   it runs as a sub-test. Where it cannot, the comment quotes a verified
   diagnostic or describes a spec-stated contract.

## 2. The sequence

The numbered files form the sequence, with two directory projects:
`16-modules/` and `37-method-import/`. "Builds on" names the pedagogical
prerequisites. Sub-test helpers are named `check-`, because `test-` names a
test function (38).

| # | Capability taught | Builds on |
|---|---|---|
| 01 | Integer literals and the four arithmetic operators | — |
| 02 | Boolean literals and comparison operators | 01 |
| 03 | Local names with `let`: sequential and nested bindings | 01 |
| 04 | Named functions with `defn`; `if` as an expression | 02, 03 |
| 05 | Self-recursion and tail calls | 04 |
| 06 | Nullary ADTs (`deftype` enums) and `match` | 04 |
| 07 | Let-polymorphism, including one definition used at several types | 04 |
| 08 | Float literals and the monomorphic float primitives | 01, 02 |
| 09 | The `String` type and basic string operations | 04 |
| 10 | Product and sum types with typed fields; generated `Type.field` accessors named | 06 |
| 11 | Pattern matching that binds constructor fields; chaining `checked-quot` through `Option` | 10 |
| 12 | Anonymous functions (`fn`) and capture | 04 |
| 13 | Functions as arguments and results; composition | 12 |
| 14 | `Vec` literals and operations; vec primitives as values through one generic helper | 13 |
| 15 | Traits, operator dispatch, constrained polymorphism, default methods | 10 |
| 16 | Multi-file programs: `mod`, specific-name `import`, qualified references | 04 |
| 17 | User-defined traits and `Display` | 15 |
| 18 | `defmacro`, quasiquote and unquote, multi-clause macros, intentional capture versus auto-gensym, declaration boundaries | 04 |
| 19 | Threading pipelines with `->` and `->>` | 18 |
| 20 | Implementing traits for user ADTs; constrained impls and finite re-entry at nested payload types | 07, 10, 15, 17 |
| 21 | The IO model: `Pure`, `bind`, combinators built from them, real console output; an IO value runs again each time it is sequenced | 04, 12 |
| 22 | Testable IO through the `test-capture` platform | 21 |
| 23 | IO sequencing with explicit `bind` chains | 21 |
| 24 | Input with `read-line`; read then process | 21 |
| 25 | Auto-currying: of a `defn`, a local closure, a trait operator and `bind` taken as a function value; first library import (`operators`) | 12, 13, 15, 21 |
| 26 | The higher-kinded `Functor` trait, for `Option` and for `IO` | 15, 10, 21 |
| 27 | Lazy sequences | 12, 13 |
| 28 | Lenient evaluation: independent `let` bindings spark in parallel | 03 |
| 29 | The `:Type` annotation model (capstone), including spaced `: Int` | 04, 10, 15 |
| 30 | A general parallel `par-map` over a `Functor` through apply-argument sparking | 26, 28 |
| 31 | Bitwise integer primitives as bitmask set operations | 01, 02 |
| 32 | Explicit-control concurrency: `sleep`, `race`, `select`, inline timeout pattern | 21 |
| 33 | Forward references within one compilation cluster; duplicate `defn` rejection | 04, 15 |
| 34 | A poll-shape platform leaf that suspends and resumes on the host reactor | 21 |
| 35 | Same-named constructors across types: dotted `Type.Ctor` in value and pattern position; `.` is never part of a binder | 06, 10 |
| 36 | Multi-signature `defn`: arity dispatch, type dispatch, defaults by overload | 05, 06, 10, 14, 25 |
| 37 | Method-import dispatch: calling a trait method needs only the method in scope; declaring an impl through a qualified trait reference | 15, 16 |
| 38 | Program tests: `test-` functions of type `(Fn [] (Option String))`, the `--test` report and exit status; a mistyped test is warned, not run | 02, 09, 11 |

### 2.1 Entry constraints

These notes prevent plausible but wrong edits.

- **11.** 10 constructs an `Option` by hand; 11 imports `primitives/Option`
  because that is the type `checked-quot` returns. Checked division handles
  expected failure as a value, including the `Int.MIN / -1` boundary.
- **21 and 22.** 21 is the complete IO introduction and the only example that
  loads `(platform stdio)`. 22 adds only the `test-capture` platform. Do not
  re-teach 21's primitives in 22.
- **29.** 29 is a capstone. `:Type` appears from 04 onward. 29 names the one
  model and shows annotations doing inference work: constraining function
  typing and disambiguating an expression.
- **30.** The per-element leaf is a tail-recursive accumulator. The top-level
  divide-and-conquer is the only intended parallelism.
- **32.** Each `race` and `select` branch is a named helper because that reads
  more clearly. The timeout pattern is written inline because stdlib `timeout`
  is outside the free-standing boundary. Per the spec, `(select [])` is a
  runtime panic that ends the process. A panic in any branch ends the process;
  cancellation does not contain it. 11 teaches checked operations instead.
- **33.** Batch definition ordering is the lesson. Live replacement across
  separate REPL inputs is a different operation, owned by the REPL and user
  guides.
- **34.** A self-driving timer leaf (`async-read` from the `async-demo`
  platform) teaches the poll-shape mechanism without a socket.
  `examples/lib/platforms/` has no `async-demo` link, so 34 needs
  `CRANELISP_PLATFORM_PATH`. If `async-demo`'s effect changes, 34 and
  `tests/concurrency_reactor.rs` change together.
- **36.** The `:(Vec Int)` clause requires `(import [primitives [Vec]])`
  because the examples prelude re-exports the vec functions but not the type.
  The element type must be concrete: `:Vec` and `:(Vec a)` are rejected.
- **37.** The two main impls live in `main/traits.cl`, because a bare
  `(impl Describe …)` needs `Describe` in scope. The entry module imports
  the methods only; its own impl names `main.traits/Describe`.
- **38.** Its dependency position is after 11. It was appended as 38 by a
  user-approved exception to the no-append rule (2026-09-30); the regroup
  (§4.5 step 5) moves it. `main` counts passing tests so the `--run` harness
  still verifies it; under `--test` it reports four `ok` lines and exits 0.

## 3. The examples-local library

[`lib/README.md`](lib/README.md) states the rules and the current contents.
The candidate modules below are unscheduled direction, not commitments. None
may land before its earning lesson exists.

| Candidate | Provides | Earned by | Relieves |
|---|---|---|---|
| `show.cl` | `Display`/`show` for primitive types | 17 | re-declaration in 20 |
| `option.cl` | `Option` with eliminators written using `match` | 10, 11 | inline `Option` declarations |
| `hof.cl` | `compose`, `flip`, `apply-twice` | 13 | — |
| `seq.cl` | `map`/`filter`/`fold` over `Vec` by explicit recursion | 13, 14 | — |
| `thread.cl` | `->` / `->>` | 19 | later examples that want pipelines |
| `io.cl` | a `do`-style sequencing macro over `bind` | 18, 23 | 23's plumbing-only framing |

When a module lands, the files that stop re-declaring its contents change
their exit codes. Batch those changes, because `test` reconciles
`tests/examples.rs` in the same change-set.

## 4. Standing assessment

The `training` contract asks this whole-sequence question every increment.
S124 (2026-11-20) re-read the sequence and local library against the delivered
language. After the bounded Phase 6b edits, at `9d18061d`, all 38 entries
matched `tests/examples.rs` in cold and warm `--run` and linked execution:
**152/152 exits matched**. 38 also reported four `ok` lines under `--test`,
exit 0. No filenames, pinned exits or console output changed. These are
teaching-material replays, not independent acceptance tests.

The replay used the private-copy environment in
[`AGENTS.md`](AGENTS.md#verification), with no stdlib path and the existing
debug compiler binary; no Cargo command ran. The source checkpoint began
at `3c5e41ca`; binary provenance was supplied by the dispatch, not established
by rebuilding. Focused probes rejected a rest name followed by another
parameter, a bracket rest parameter and an integer-valued macro body; their
valid rest and syntax-returning controls each returned 42. A focused root-result
probe found "42" under both `--run` and linked execution (exit 41); 21 retained
its seven-line transcript and exit 250. Dated probes below retain their dates
where their specific scenario was not repeated.

**Verdict.** Every entry runs, but the sequence is not comprehensive or yet
the best learning order. The early core progression works; the tail follows
delivery order and interleaves subjects. 01 now orients the reader to `Pure`;
18 contrasts deliberate capture with private generated bindings; 20 teaches
nested constrained implementations; 25 uses `bind` as a partially applied
function value; 28 and 30 explain strict evaluation during tracing. These
repairs improve negative-space teaching and readability without completing
the redesign below.

The stdlib's new collection instances, `derive`, `vec-flatten` and `par-*`
changes do not enter this free-standing sequence. They belong to stdlib
learning material. A dedicated tracing lesson remains held on
[S124-Q13](../spec/appendix-d-open-questions.md#s124-q13-what-are-a-trace-roots-name-parameters-and-children):
ACT-1094's result correction has landed, but the root's name, parameters and
shape are unsettled. The other open trace questions are recorded in
[tracing §6](../design/arch/tracing.md#6-nested-trace-guard); do not teach their
answers as settled. Current defect evidence is maintained by `qa` in
[the S124 evidence delta §14](../tests/plan/s124-evidence-delta.md#14-the-standing-state).

### 4.1 Coverage gaps

| Gap | Spec | Evidence | Notes |
|---|---|---|---|
| **A1** The full error model: panic sources and process termination in every mode, errors encoded in types, wrapping arithmetic, `Inf`/`NaN` | §12.7, App A.3 | S123: 11 teaches checked division and contrasts unchecked `Int.MIN / -1` wrapping; 32 explains process termination for branch panics | Checked failure cases run; panic sources still need teaching as a subject (§4.3) |
| **A2** Generated `Type.field` accessors as the idiomatic single-field read. 10 names them; no example uses them. The boundary to teach is that accessors are minted for product fields only, while sum-constructor payload labels mint none | §5.2.6 | S115 probe; spec settled S121 | A corpus-wide style pass, not one beat |
| **A4** Module visibility and the import/export surface: private `-` forms and the private-import rejection, `export`/re-export, glob, member, alias and renamed imports, `super`, shadowing and conflict | §8.3–§8.7 | scan 2026-09-22: no `defn-`, `(export`, or `[*]` in any example | Grow `16-modules/` |
| **A5** The string surface beyond basics, including `parse-int` to `Option` as the fallible-input idiom | App A.3, §12.1.2 | scan 2026-09-22: 09's comment defers these | Extend 09; no `Byte`/text examples until those facilities ship |
| **B1** Pattern-matching negative space: nested, literal and or-patterns, guards; exhaustiveness as a compile-time rejection | §6.5–§6.6 | S115 | Comment-grade plus the boundaries example |
| **B4** String byte length versus character length | §12.1.2 | S115 | — |
| **B5** Strict left-to-right evaluation, named as the contrast for 27, 28 and 30 | §12.4.1 | S115 | Prose beat |
| **B6** Detached strands, launch-and-continue, cancellation and draining; any strand's panic ends the process | §10.12.7, §12.7.9 | S122: the cancellation-context and drain obligations are marked uncovered in the spec; S123: panics terminate the whole process | Wait for evidence of the delivered behaviour |
| **B7** Docstrings in all six positions | §5.2.5, §5.12, §7.1.2, §9.2.4 | S115 | — |
| **B7a** Reader surface: string escapes, comma as whitespace, `'form`, `#(… %1)` | §1.2–§1.5 | S124 scan: no string-escape or shorthand-lambda lesson; auto-gensym is taught in 18 | — |
| **B7b** `trace` and the `Trace`/`TraceCall` ADT | §2.3.10, §4.12.4 | S124: 28 and 30 explain strict trace evaluation; no executable trace lesson | Held on S124-Q13; the landed root-result fix alone does not settle root shape |
| **B8** Sexp and macro surface: nested quasiquote, `begin` expansion, zero-argument macros, SList helpers. 19 explains the rest marker and `~@` in one note only | §9 | S115 | — |
| **B10** Explicit trait constraints; operators as values beyond 25's partial | §7.6, §7.8.2 | S115 | — |
| **C2** Network poll shape (accept, read, send) | — | FIXME 0463 (open) | Needs a reusable, deterministic socket platform. 34 teaches the mechanism meanwhile |

Out of scope by the library ruling: the stdlib prelude vocabulary (`do`,
`cond`, `derive`, `List`, `Map`, `Set` and similar) belongs to the stdlib docs.

### 4.2 Order

The early core has a designed progression. 01 orients readers to the `Pure`
entry-point wrapper before the full IO introduction at 21. 21–38 were
appended in delivery order, so position does not signal difficulty. For
example, 31 needs only 01–02, and
25–27 sit inside the IO arc. Two specific defects:

- 29's capstone content is a prerequisite for 11, 26, 35, 36 and 37. A short
  "annotations pin types" beat after 10 would let 29 stay the capstone.
- 15, 17 and 19 each declare traits from scratch without saying why. The
  library (§3) removes the repetition.

A defensible regrouping: core (01–14, with 38 after 11), traits (15, 17, 20), modules (16, A4),
macros (18, 19), functions as data (12, 13, 25–27), IO (21–24, 34),
concurrency (28, 30, 32), language mechanics (29, 33, 35–37), errors (A1).
Renumbering renames the files `tests/examples.rs` pins, so it is a separate
change co-planned with `test`, and it comes after the content gaps close.

### 4.3 Negative space

Boundary teaching is concentrated in 11, 18, 20, 29 (the strongest boundary
writing), 32, 33, 35 and 36. No example has a boundary as its subject. A
runnable example cannot contain a type error, so compile-time boundaries can
only be comments, and comments go stale unobserved. S115 found six false
comment claims, all corrected then. S124 adds verified macro-declaration
refusals and a running capture-versus-gensym contrast in 18. Checked operations
let expected failures run as sub-tests: 11 matches the `Option` from checked
division. A runtime panic ends the process, so panic demonstrations require separate executions
rather than sub-tests that continue afterward. A boundaries example should
follow A1 and gather §6.6's prohibitions,
exhaustiveness, the binder rules, the annotation traps and ambiguity.
S123 checked ACT-1017 at its source filing: both its failed-dependency
location and duplicate-prefix faces are resolved. S124 re-read ACT-1036's
source filing: the non-IO `main` location is corrected; the remaining case
is a macro-produced function restored from cache that references
`discover-tests`. That residual does not block the
ordinary boundary lesson. Re-probe any diagnostic before quoting it.

### 4.4 Readability

- **Every `main` is written for the harness.** Each file ends in a nested
  `add-i64` staircase: 30 levels in 15 and 22 in 20 (S115).
- **Most exits are checksums, not pass counts.** The conventional pass count
  in `AGENTS.md` holds in only a few files, such as 08, 31–34, 36 and 37. Several sub-tests contribute 0 on success, 02 and 20 among
  them. In 20 the signal is inverted: a regression would raise the total.
- **Boilerplate.** The `;; Wrap the sum-of-pass-counts in Pure …` block
  appears in 27 files (scan 2026-09-22).
- **Weakest files.** 20 spends most of its length on monomorphic manual
  implementations before its constrained example. 15 is long and repeats
  setup. More than half of 19 builds the threading macros before using them;
  its pipeline and insertion-point comments are now correct. 27 implements
  a lazy library rather than using one.
- **Library recap.** The prelude summary now states its purpose without a
  primitive count; `operators.cl` distinguishes its explicit `Ord` methods
  from 15's defaults. The earning rule and free-standing boundary remain.
- **34's overlap claim.** Its final section describes overlapping waits,
  but the second `async-read` is constructed inside the first `bind`'s
  continuation. That is sequential IO under §10.3, and the value-only
  check cannot observe overlap. Correct this teaching claim in a separately
  scheduled edit; the current bounded plan does not change 34.
- **House style.** 29, 33 and 37 show the standard to bring the rest to.

### 4.5 Direction

The broader sequence work below is unscheduled. `sprint` schedules it and the
user approves the phase. Each step should leave the sequence green:

1. A1, then the A2 corpus pass.
2. A4 and A5, which are independent of each other.
3. The boundaries example, which needs A1, with B1, B4–B5 and B7, building
   on 18's hygiene lesson.
4. The library candidates, each alongside its earning lesson (§3).
5. Regroup and renumber, normalise every `main` to an honest pass count, and
   replace the repeated boilerplate with one note. Do this last, with `test`.
   Decide with `qa` and `test` whether sub-test checks become test functions
   run under `--test` (38) instead of a checksum `main`.

**Anti-goal:** do not close gaps by appending files 38, 39 and so on.

### 4.6 Pending example edits

Each item needs an authorized example edit. Include it in the next change to
the file it names.

- **37: no-impl diagnostic comment.** Calling `describe` on a type without
  an impl is rejected with `no impl of trait main.traits/Describe for type
  main/Hex` (probe 2026-09-30). Re-probe the full diagnostic before quoting
  it; ACT-1036 concerns a different refusal and does not block this edit.
- **Not a beat: a non-`Int` program result.** It is legal and exits 0
  ([spec §10.6.1](../spec/10-io.md)), so an example whose
  `main` does not return `Int` cannot verify itself.
