# S124 evaluation: the Rust context standard in cranelisp

**Owner:** `arch`. **Reader:** the user, deciding later whether to adopt the
shared package's Rust context standard, part of it, or neither.
**Status:** evaluation, 2026-11-16. It decides and changes nothing; the
standard stays unadopted for S124 by the user's ruling.
**Checkpoint:** `main` at `3155f47f` plus the uncommitted Phase 2 documents;
package pin `cfc0a4e`.
**Retention:** working document. Retire it once the adoption decision is
recorded in root guidance, or at the close of the sprint that takes it.

The evaluation was read-only. No source, test, specification or memory was
edited, and no build or suite ran. §8 lists what was run and opened.

## Recommendation

Do not adopt the standard as written. Adopt one part of its mechanical check,
the declared dependency edges, in a later sprint. Take two of its
documentation ideas as ordinary `arch` and `design` work without adopting the
standard.

| Option | What it buys here | What it costs here | Position |
|---|---|---|---|
| Full adoption | Nothing the repository lacks except the two items below | A `Facade` trait and `init` in six crates that have no state to initialise; six crate-root designs; about 1,700 citation edits | Decline |
| Dependency edges only | The crate graph becomes measured for all 18 workspace crates, where one edge of it is measured today | One table in `.agents-consumer.toml`; one line in the wiring verifier; a recorded exception for using the "supporting" kind | Recommend, later sprint |
| Documentation ideas only | A direct route from root guidance to each context's design; fewer carriers per fact | A six-row table; the existing audit dispositions | Recommend as ordinary work |
| Continued non-adoption | No change | The reverse primitives-to-backend ban stays asserted by a comment | Acceptable; the residual is small |

The tradeoff in the recommended path: declaring the six bounded contexts as
"supporting" crates uses the tool against its vocabulary. The alternative that
avoids it is a 30-line in-repo test over `cargo metadata`, which costs
maintenance the shared tool does not. §6 sets both out.

## 1. What the standard is

The [standard](../.agents/standards/rust-contexts.md) has three separable
layers. Its adoption text treats them separately: adopting the standard does
not adopt the check, and the check passes silently until declared.

| Layer | Content | Binding element |
|---|---|---|
| Architecture model | One crate per context; a `Facade` trait as the one callable contract; a free `init`; adapters per transport; a configuration record; a private `Repo`; authority values | `pub trait <crate>::Facade` and `<crate>::init` in every context crate |
| Documentation layout | Root guidance introduces each context and links its `DESIGN.md` at the crate root; rustdoc carries the callable contract; no separate interface document | `DESIGN.md` beside each context's manifest |
| Mechanical check | [`check_rust_contexts.py`](../.agents/tools/check_rust_contexts.py) over a `[rust-contexts]` declaration | Every workspace crate classified; exact dependency edges; facade shape read from the committed inventory |

The standard governs context crates only. A supporting crate (shared
vocabulary or capability) carries no facade obligation, and the check reads no
inventory for it.

## 2. Fit, requirement by requirement

### 2.1 Architecture model

| The standard requires | Cranelisp today | Verdict |
|---|---|---|
| One crate per bounded context | Six context crates, one vocabulary crate, the binary with its bundle ([bounded contexts](../design/arch/bounded-contexts.md)) | Met |
| Dependencies form a DAG; nothing depends on an executable | Same graph, stated in the bounded-context dependency table | Met; see §4.1 for how much of it is measured |
| Shared vocabulary in a crate beneath its users | `cranelisp-types`, with a placement rule ([Principle 15](../design/arch/principles/15-facade-types-live-with-behavior.md)) | Met, with a stricter rule than the standard's |
| A reverse callback has a consumer-side contract bound by the root | `MacroExpander`, `CodeStore`, `LinkerStore` in the types crate, implemented above | Met |
| Publish the narrowest surface a consumer needs | `pub(crate)` default and the user gate | Rule met; realization short (§4.3) |
| `pub trait Facade` at the crate root, one callable contract | No crate publishes one. Surfaces are free functions, types, constants and one macro | Conflict |
| Free `init` returning `impl Facade` | None. No context crate has construction-time state | Conflict |
| Consumers take `Arc<F: Facade>`; substitutes for testing | Consumers call functions directly; tests run the real crates | Not applicable |
| Adapters, configuration record, `Repo`, routes, pages, notification, authority values | None exist | Absent capabilities; the standard says to omit them |

The standard anticipates computational crates: "a computational context can
implement its facade with a stateless value; do not invent deployment
configuration or shared state". That removes most of the service vocabulary
from scope. It does not remove the trait and `init`. Those two are what the
check enforces, and they are where the model does not fit:

- **Three of the six contracts are not Rust calls.** Intrinsics is reached
  from emitted code as stable-ABI symbols (21 `#[no_mangle]` exports, resolved
  by address). Platform is a C-ABI contract for out-of-tree DLL authors,
  largely a derive macro and layout types (124 public methods on 30 types, 7
  free functions). Primitives publishes a static table (one static, no
  function). A `Facade` trait cannot carry a symbol address, a `#[repr(C)]`
  layout or a macro.
- **The other three would gain a forwarding trait.** Frontend publishes 16
  crate-root free functions, typecheck 8, backend 4 with 40 methods. All are
  stateless transformations. A trait over them would forward to the same
  functions, and `init` would return a unit value. The standard itself says
  every wrapper must own a distinct responsibility; the shared quality
  standard says the same of thin units. This one would own none.
- **The substitution benefit has no taker.** Trait-generic consumers exist so
  an adapter can run over a substitute. The binary is the only composing
  consumer, and the suite's discipline is to run the real pipeline.

### 2.2 Documentation layout

| The standard requires | Cranelisp today | Verdict |
|---|---|---|
| Root guidance introduces each context and links its design, or one context index | Root layout table links `design/CLAUDE.md` and each crate memory; the bounded-context statement is the index | Partly met: three hops to a design master |
| One authoritative `DESIGN.md` at each crate root | One master per context under `design/{context}/`, with subordinate subjects | Met in substance; different location |
| Architecture's boundary statement may sit beside the design, one owner per fact | Bounded-context sections owned by `arch`; interiors owned by `design` | Met |
| Rustdoc carries the callable contract; no duplicating interface document | Rustdoc plus `public-api.txt` as evidence; facade-spec files retired | Met |
| Unit tests in separate files beside their implementation | 102 separate test-module declarations, 27 files with inline test modules, across the seven library crates | Mostly met; governed by [Principle 23](../design/arch/principles/23-tests-mirror-module-composition.md) |
| Standing documents describe current state without sprint history | Same rule in the project method | Rule met; realization short (§4.2) |

Cranelisp's layout differs in one structural way. The standard's reader goes
root guidance → crate `DESIGN.md` → source. Cranelisp's reader goes root →
`design/CLAUDE.md` → `design/{context}/CLAUDE.md` → master. No root line links
a design master directly, and no crate memory links the bounded-context
statement except primitives'.

### 2.3 Mechanical check

| The check requires | Cranelisp today | Verdict |
|---|---|---|
| Every workspace crate classified | Not declared. 18 packages: the root, 8 under `crates/`, 9 platform DLL crates | New declaration |
| Exact declared edges per crate | Stated in prose; one edge guarded by a test | Gap (§4.1) |
| A committed inventory per context | Seven guarded baselines plus an unguarded eighth for the bundle | Exceeded: the guard fails on drift |
| `Facade` and `init` shape in the inventory | Absent | Conflict, as §2.1 |
| `DESIGN.md` beside the manifest | Absent | Conflict, as §2.2 |

## 3. Measurements

All runs used `--declaration` and `--metadata` against scratch files, so the
repository was not modified. Scratch directory:
`/tmp/claude-501/-home-alilee-cranelisp/8d27f381-f1ba-4ea1-88ae-561177bcd23a/scratchpad/s124-arch-contexts/`. <!-- doc-check: literal reason="Session scratch path outside the repository" -->

| Run | Declaration | Result |
|---|---|---|
| As committed | None | Exit 0, "not adopted; nothing to check" |
| A | Root library plus 17 supporting crates, edges copied from the bounded-context table | Exit 0: 18 crates classified, 18 hold exactly their declared edges |
| B | As A, with the six contexts declared as contexts | Exit 1: 18 findings, three per context (no `DESIGN.md`, no `Facade`, no `init`) |
| C | As A, with backend's platform edge omitted from the declaration | Exit 1: one `edge-undeclared` finding naming backend and platform |

- **Run A is also a measurement of the record.** The dependency table in the
  bounded-context statement matches Cargo for every crate today.
- **Run C is the detection leg and run A the silent leg** for the edge rule.
  The package carries its own test file for the tool.
- **Run B read the existing baselines without complaint.** Each begins with
  the crate's `pub mod` line, which is the tool's test that an inventory is
  usable.
- **Cost of a run:** 0.05 s with captured metadata. It needs Cargo and no
  build.
- **The consumer check accepted the scratch table.** `check_consumer.py`
  raised no declaration fault for `[rust-contexts]`.

Sizes that bear on migration:

| Quantity | Value |
|---|---|
| Baseline lines: types / backend / platform / intrinsics / typecheck / frontend / primitives | 2,333 / 557 / 543 / 289 / 146 / 69 / 10 |
| Context design trees: files, lines | backend 22, 8,166; typecheck 22, 7,811; int 29, 14,038; intrinsics 6, 2,418; frontend 12, 1,865; platform 5, 1,393; runtime 2, 768; primitives 1, 463 |
| Citations of a context design path from outside its own directory, all eight trees | 2,026 lines in Rust sources, 614 in live Markdown, 787 elsewhere |
| The same, for the six context crates' trees only | 1,096 Rust, 305 live Markdown, 276 elsewhere |
| Citations of the bounded-context statement | 123 Rust lines, 193 live Markdown lines; 99 Rust lines cite a numbered invariant |
| Crate memories | 99 to 276 lines each, 1,693 in total with the binary's |
| Commits that changed a workspace dependency line in a crate manifest | 18 in the project's life; the last real edge change was 2026-06-13 |

## 4. What it would prevent or detect here

### 4.1 The crate graph is asserted more widely than it is measured

- The bounded-context statement says "Cargo enforces this graph". Cargo
  enforces that a crate uses only what its manifest names, and that the graph
  has no cycle. It does not compare a manifest with the table.
- One consequence is structural: no library can depend on the binary, because
  the binary depends on every library and Cargo rejects the cycle.
- One absence is measured: backend does not depend on primitives
  (`crates/cranelisp-backend/tests/no_primitives_dep.rs`, a substring test on
  the manifest).
- **The reverse absence is not measured.** The statement calls the ban
  load-bearing "in either direction". Primitives depending on backend creates
  no cycle, and nothing fails if the line is added. That edge existed until
  the S73 close removed it. Today a rustdoc sentence in the primitives crate
  root is its only carrier.
- Every other edge is graded by inspection: a new manifest line is visible in
  review and procedurally gated as a new consumer edge, and nothing executes.
- **History.** Backend's direct platform edge arrived in an S81 feature
  commit (`d1949fbf`) with its rationale in a manifest comment. Whether it
  passed an approval gate was not determined (§7).
- **Residual.** Low likelihood: two real edge changes since the May runtime split. Moderate
  impact: the dispatch invariant that the ban protects is structural only
  while the edge is absent. The declared-edges check closes it for all 18
  crates at the cost in §5.2.

By root guidance's own grades, this moves the graph from asserted to measured,
with the detection proof in §3.

### 4.2 Design carriers per fact

Both audit assessments on file found the same class of defect:

- Backend (S122): eleven status claims went stale in one commit; 15 of about
  45 sampled source claims were stale or false; at least ten rule families
  were stated in two to four homes; the crate memory restated design and
  carried false claims.
- Frontend (S123): the crate memory, master design and crate-root rustdoc
  disagreed with source and with each other on five named points.

A cranelisp fact about one context can live in five carriers: its
bounded-context section, its design master, a subordinate design, the crate
memory and rustdoc. The standard has two (the crate design and rustdoc), with
a local memory only for working instructions.

- **What the standard would contribute:** the rule that a context has one
  integrated design and that a local memory carries no design.
- **What it would not contribute:** enforcement. The check tests only that
  `DESIGN.md` exists. The decay the audits found is in prose, which no
  checker here reads. Cranelisp's method already states the same rule; the
  shortfall is in keeping to it, and the audit dispositions own that.
- **Moving the files would not reduce the carriers.** The count falls only if
  crate memories and bounded-context sections stop restating design, which
  can be done where the files are.

### 4.3 Public surface without consumers

- The backend audit estimated that 25–30% of backend's top-level public items
  have no live consumer. The S124 review found `CompileContext` public with no
  outside consumer.
- The standard's model would prevent this by construction: everything outside
  the one trait is private.
- The check would not detect it. It judges the facade's shape and says nothing
  about other public items or modules. Backend's 16 public modules would pass
  if a `Facade` and `init` were added beside them.
- The existing controls reach this better: the baselines make every item
  visible, the user gates every change, and the audit rotation finds
  consumerless items. The gap is landing approved contractions (review §8.6),
  which no standard changes.

### 4.4 What it would not have caught

None of the three assurance failures root guidance records (register row R11,
invariant I-CT, the drop-glue registry) is a boundary-shape or
dependency-direction failure. Each was a property inside one crate that
nothing executed. The standard has no bearing on that class.

## 5. Cost

### 5.1 Full adoption

| Work | Size | Owner | Gate |
|---|---|---|---|
| `Facade` trait and `init` in six crates, and consumers moved onto them | About 480 lines in the binary that name one of the six crates, plus cross-crate callers; seven baselines regenerated | `arch`, then `dev` per crate | User gate on every row; serial source editing |
| Six crate-root `DESIGN.md` files | Move or front the masters; the binary, the bundle and the shared runtime pair have no context crate to hold theirs | `design` | Ownership change: `design`-owned files inside `dev` directories |
| Citations of moved design paths | About 1,700 lines for the six trees, 1,096 of them in Rust sources | `dev`, serially | None; pure churn |
| Root guidance context table and adoption statement | Small | `sprint` | User |
| Declaration and check wiring | As §5.2, plus shape rows | `arch`, `sprint` | User |

- A design that stays where it is, with a pointer file at the crate root,
  would satisfy the check and add six files that state nothing. The shared
  document contract warns against establishing documents to make a command
  green.
- The facade work would be an interim architecture in the sense of
  [Principle 8](../design/arch/principles/08-no-interim-implementations.md)
  only if a later capability needed it. None is planned.
  [Principle 6](../design/arch/principles/06-complexity-has-a-budget.md)
  applies directly: the trait is cost with no consumer.

### 5.2 Dependency edges only

| Work | Size |
|---|---|
| `[rust-contexts]` table: root library plus 17 supporting crates with edges | About 45 lines; the scratch declaration for run A is the draft |
| One invocation in `scripts/verify-role-wiring.py`, or beside it | One line |
| Root guidance: the adoption scope and the exception below | A short paragraph |
| Bounded-context dependency table | Keep as the rationale; name the declaration as the checked copy |
| Retire `no_primitives_dep.rs` | Optional; the declaration subsumes it |

Upkeep: one declaration edit whenever an edge changes, which the record
shows is rare (twice since May). A stale declaration fails the check, so it cannot decay silently.

**The exception to record.** The standard defines a supporting crate as one
that "manifests no context". Declaring frontend, typecheck, backend,
primitives, intrinsics and platform that way is false to its vocabulary. It is
the only classification under which the tool checks edges without demanding a
facade. Root guidance would state that cranelisp adopts the dependency rules
only and that its contexts are declared as supporting for that reason.

**The upstream alternative.** A context kind that declares edges and no facade
shape would make the declaration truthful. That is a package contribution,
ratified against the other consumers, and belongs to a close.

### 5.3 Documentation ideas only

- Add a context table to root guidance: context, responsibility, design
  master. Six rows, linked directly. It shortens the route from three hops to
  one without moving a file.
- Hold crate memories to working instructions, as the method already says.
  The two audit dispositions carry the specific repairs.

## 6. What would be lost

### 6.1 Under full adoption

- **Stable citation targets.** Source and tests cite "§N invariant M" 99
  times. Splitting the bounded-context statement into per-crate files moves
  every one. The standard permits keeping a single context index, so this
  loss is avoidable, but then the per-crate design is not the integrated
  document the standard describes.
- **The owner split by directory.** `design/` belongs to `arch` and `design`;
  `crates/` to `dev`. Narrow deployment, source reservations and the
  single-writer rule lean on that split. Crate-root designs put two owners in
  one directory.
- **Designs that span crates.** The binary's design (29 files, the largest
  tree) covers `src/` and the bundle. The runtime-pair contracts cover
  primitives and intrinsics. Neither has one crate root to live at.
- **Direct calls.** Every consumer call would go through a trait that adds no
  meaning.

### 6.2 Under the dependency check alone

- **One more copy of the edges.** The graph would be stated in the manifests,
  the bounded-context table and the declaration.
  [Principle 7](../design/arch/principles/07-single-source-of-truth.md)
  is satisfied only if the declaration is the approved copy, the manifests
  are checked against it, and the table cites it for the edges.
- **A dependency on the tool's vocabulary** that does not describe cranelisp,
  until the upstream alternative exists.

### 6.3 The in-repo alternative

A test over `cargo metadata` asserting the full edge table would give the same
grade with no borrowed vocabulary. It costs a test to write, prove and
maintain, where the shared tool is already pinned and tested. The wider
control is the same in both; the choice is between a recorded exception and
owned code.

## 7. Corrections to the Phase 2 review, and limits

The [review](s124-architecture-review.md) §6 gave three reasons to stay
unadopted. Tested against the sources:

| Review claim | Finding |
|---|---|
| The check "would add a second public-API inventory beside `public-api.txt`" | **Wrong.** The tool reads `public-api.txt` beside each manifest by default, and run B read cranelisp's files as they are. The standard names different generation flags, and none of the tool's rules depend on the difference |
| The standard "assumes service-shaped contexts" | **Overstated.** It has explicit provision for computational contexts and for omitting absent capabilities. What remains mandatory is the trait, `init` and the crate-root design. The conclusion stands on those three, not on the service vocabulary |
| "Cranelisp already holds the same properties" | **True with one exception.** The dependency graph is asserted for more than is measured (§4.1) |

The recommendation to stay unadopted survives. Its first reason does not, and
the review missed the one check worth having.

Not determined:

- Whether the S81 backend-to-platform edge was approved before it landed, and
  whether the consumer-edge clause of the public-API gate existed then.
- Whether the Claude host follows a root-guidance link to a crate design as
  reliably as it loads a directory memory. The standard's own test for
  usability is a fresh agent's bounded change; none was run.
- The exact number of call sites a facade migration would touch. The figures
  in §5.1 count lines that name a crate path, which overcounts imports and
  undercounts glob uses.
- Whether another consumer of the package would accept a facade-free context
  kind.
- The tool against regenerated inventories. Only the committed baselines were
  read; ACT-0955's format change removes auto-trait lines, which no rule
  reads.

## 8. What was run and opened

| Purpose | Run or opened |
|---|---|
| The standard and its adoption steps | `.agents/standards/rust-contexts.md`; `.agents/CONSUMING.md` §Machine declaration, §Adopt an engineering standard; the checker source in full |
| Workspace facts | `cargo metadata --no-deps --offline`, captured to the scratch directory |
| Checker dry runs | `python3 .agents/tools/check_rust_contexts.py --root . --declaration <scratch> --metadata <scratch>` for runs A, B and C; once with no arguments |
| Declaration acceptance | `python3 .agents/tools/check_consumer.py --root . --declaration <scratch>` |
| Current arrangement | Root guidance; `design/arch/CLAUDE.md`; the bounded-context statement's dependency table and section openings; each `design/{context}/CLAUDE.md`; `tests/CLAUDE.md` §Public-API enforcement; `tests/public_api_relocations.rs`; `sprints/METHOD.md` §3.1 |
| Surfaces | Line and item counts over the eight `public-api.txt` files; crate-root `lib.rs` sizes; `#[no_mangle]` counts |
| Citations and layout | `git grep` counts of design paths, bounded-context citations and test-module declarations |
| Edge history | `git log -G` over crate manifests; `git show` of `d1949fbf`, `ef69ede5`, `e7470e17`, `701a5f20` |
| Existing edge guard | `crates/cranelisp-backend/tests/no_primitives_dep.rs`; a search of the primitives crate for a reverse guard |
| Audit evidence | `audits/cranelisp-backend-s122.md` F6, F7, F11; `audits/cranelisp-frontend-s123.md` R5 |
