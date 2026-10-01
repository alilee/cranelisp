# cranelisp-backend — S122 whole-context assessment

| | |
|---|---|
| Context | `cranelisp-backend`: `crates/cranelisp-backend/`, `design/backend/`, and both local memories |
| Increment | Sprint 122, Phase 6a (rotation audit, `sprints/archive/sprint-122.md` "Audit") |
| Checkpoint | `88bbbd12` on `main`; the audited surfaces were clean against it throughout |
| Date | 2026-09-30 |
| Predecessor | S110 assessment, recoverable at [`57253cf2:audits/cranelisp-backend-s110.md`](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-backend-s110.md). Its undisposed residue is carried by [ACT-0964](../sprints/actions/ACT-0964-backend-audit-residuals.md) and the backend row of [ACT-0969](../sprints/actions/ACT-0969-next-rotation-audit-inputs.md) |
| Disposition | **Pending.** Every recommendation in §8 awaits S123 Phase 1 with the user. Nothing here approves work, accepts a residual or resolves a defect |

This is dated evidence, not design or requirement authority.

---

## 1. Verdict

### 1.1 Requirement fulfilment

**Not fulfilled.** One language MUST is violated by an observed fault. A second
is violated by construction in source. The rest of the context's obligations
are met.

| Requirement | State | Evidence |
|---|---|---|
| [Runtime model](../spec/12-runtime.md) §12.3.1 item 2: freed memory is not accessed. §12.7.8 item 4: no use-after-free | **Not met** | **Observed.** This audit re-ran `tests/vec_push_match_binder_same_name_shadow.rs` at `88bbbd12`. Its control aborts with `USE-AFTER-FREE: vec op vec_push_copy(src) touched data buffer … freed (previous free site = vec_drop)`. That is [ACT-1030](../sprints/actions/ACT-1030-let-wrapped-tail-forward-uaf-intake.md). **Predicted and unmeasured:** leads L2, L4, L5, L6 (ACT-1030's face), L10 and [ACT-1029](../sprints/actions/ACT-1029-alias-map-same-name-overwrite-lead.md) (`design/backend/ownership-codegen.md` §13.3). See also finding F4 |
| [Runtime model](../spec/12-runtime.md) §12.7.2.1: `vec-set` with an index `< 0` or `>= length` panics | **Not met (source)** | `compile_vec_set` and `emit_vec_set_cow_core` (`compiler/vec_codegen.rs`) have no index check. The in-place arm loads the old element at `data_ptr + idx*8`, RC-decrements it and stores the new value, all under `MemFlags::trusted()`. The copy extern `vec_set_copy` (`crates/cranelisp-intrinsics/src/vec_runtime.rs`) drops the new value silently when the index is out of range. Only `emit_vec_get_core` checks bounds. The spec row is still `[S18]`; no test has ever exercised it. Not executed by this audit (F2) |
| §12.3.1 item 1: heap values are freed when unreachable | **Partially met** | Carried leaks: [ACT-1026](../sprints/actions/ACT-1026-binder-forwarding-join-consumed-in-frame-leak-intake.md) (+1 per evaluation, exposure widened by the S122 COW correction), [ACT-1028](../sprints/actions/ACT-1028-let-bound-vec-set-returned-leak-intake.md), the [ACT-1022](../sprints/actions/ACT-1022-match-arm-branch-push-residual-lead.md) lead. Non-concrete faces 2 and 3 are said to "leak today" (`crates/cranelisp-backend/CLAUDE.md`; `rc_emission.rs::signature_heap_category` rustdoc). Nothing measures that claim (F5) |
| [Runtime model](../spec/12-runtime.md) §12.5: self tail calls run in constant stack | Met | `[Tested+Neg]`; five `spec_12_runtime` cells |
| [Runtime model](../spec/12-runtime.md) §12.7.2: runtime faults lower to `runtime/panic`, with the spec's messages and no hardware trap | Met, except `vec-set` | No `.trap(`, `trapz` or `trapnz` in the crate. `"match failed"`, `"division by zero"` and `"vec-get: index out of bounds"` match the spec table |
| BC §3 invariant 1: one emission path | Met | `compile_to_module` is the only emission entry |
| BC §3 invariant 2: uniform consuming convention | Met | `compiler/entry_convention.rs` derives it once from `Life × Realization`, with no `_ =>` arm |
| BC §3 invariant 9: only concrete types reach RC classification | **Partially met** | `signature_heap_category` still maps `Err(_) ⇒ HeapCategory::Mixed`. Register R17 is `unasserted` and R18 is open. The structural close is designed but not built (`non-concrete-release-contract.md` §7.2–§7.4) |
| [Bounded contexts](../design/arch/bounded-contexts.md) §3 invariant 10: pure keyed consumer | Met | Resolver entry points: zero. The four `symbol_tables.iter()` sites are enumerations (`jit.rs` ×2, `trace_codegen.rs`, `utilization.rs`). ACT-0964's soft arms are still present, as that filing records |
| Cache trust boundary | Met within the user's posture | One validation loop (R6, proven). The user accepted corrupt-cache residual risk on 2026-09-24 (SPRINT "C-A disposition"). `cache/linker.rs` panics on truncated relocation offsets inside that residual |

### 1.2 Maintenance-economy grade: **D**

The avoidable weight is systemic. It sits on the core path, reference-count
emission, and it multiplies four other layers: evidence, documentation, review
and coordination. The pattern spreads, and the S122 record shows it
compounding. Each defect adds one more predicate, test file, design section and
local-memory row. Development remains practicable: outside the ownership stratum,
ordinary changes are still local.

That boundary is what keeps the grade above F. The grade is not averaged with
the strengths in §7. Correct individual predicates and discriminating tests do
not lift it.

### 1.3 Per-attribute verdict (the [acid test](../sprints/METHOD.md#27-rolling-whole-context-audit))

| Attribute | Verdict | Grounds |
|---|---|---|
| Design quality | **Split** | **Strong:** the boundary (keyed consumer), one emission path, `DropGlueRegistry`, the entry convention and the cache validation loop. **Weak:** ownership emission. The design encodes per-shape rules and lists its own predicted use-after-free leads (§13.3 L2–L10) |
| Design realisation | **Weak** | Three ratified designs are unrealised or silently narrowed: the S114 one-classifier consume contract (`binding-indirection-consume.md` §1) still keys call arguments on `MonoExpr::Var` syntax; the S121 "one slot per binder, never per name" rule still has name-keyed borrow roots and last-use maps; the S119 option-2 measurement gate never ran. Eleven status claims say the checkpointed code is "uncommitted" |
| Simplicity and volume: code | **Weak** | 29,776 production lines, up about 35% on S110's ≈22k. 10,645 of those lines are comments; in `fn_compiler.rs` production code comments are about half. 785 sprint, FIXME and ACT references |
| Simplicity and volume: documents | **Weak** | 9,777 lines in `design/backend/`. About 7,600 lines must be read before changing a release seam. Three sprint-named records and three work orders sit in the standing tree |
| Simplicity and volume: tests | **Adequate in volume, weak in shape** | 618 unit tests, 25,706 lines. About 45 RC/memory-safety e2e files. One file per defect; about 15 local CLIF wrappers beside about 12 shared harness entry points |
| Duplication | **Adequate in code, weak in documents** | Code: one glue authority, one entry convention, one nullary guard. Documents: at least 10 rule families stated in two to four homes (§6 F6) |
| Risk-weighted coverage | **Weak on the top risk** | Every S122 use-after-free was found incidentally. The generator and the differential oracle are blind to this class (§6 F3). `vec-set` bounds have been untested since S18 |
| Maintainability | **Weak in the ownership stratum** | `FnCompiler` has 28 fields, 12 of them ownership state. 13 separate answers to "who owns this reference". Rustdoc is spliced onto the wrong functions (§6 F8) |
| Memory freshness | **Weak** | `crates/cranelisp-backend/CLAUDE.md` makes at least six false or stale claims (finding F7). `design/backend/CLAUDE.md` is sound |

### 1.4 The acid-test answer

**Would a second, informed build look like this? At the boundary, yes.**
Emission entry, keyed consumption, glue identity, the entry convention and cache
validation are what retained insight would build again. The S110 answer stands.

**In the ownership stratum, no.** A second build would not decide ownership
separately at each emission site from the syntax of the expression in hand.
That design has produced a steady series of defects: 0810 (ten faces), 0917,
IOR-5, then S122's ACT-0974, ACT-1021, ACT-1024 and ACT-1027. ACT-1030 is still
open, with eight leads behind it. The project analysed this cost structure in
S119 ([ownership-stratum options](../design/arch/ownership-stratum-options.md)).
Option 2's adoption was deferred to "S120, on the number", but no sprint took
the measurement.

---

## 2. Boundary, sources and method

- **Boundary.** `crates/cranelisp-backend/`, `design/backend/` (including
  `archive/`) and both local memories. Cross-context documents were read only
  where they govern this context.
- **Requirement sources, read first.** `spec/12-runtime.md` (normative §12.2,
  §12.3, §12.5 and §12.7); `design/arch/bounded-contexts.md` §3; the
  [safety register](../design/arch/safety-invariants.md) rows that name the
  backend; the [ownership spine](../design/arch/ownership-inference.md) §6.2.
- **Independence.** The brief's list of S122 faults and actions was treated as
  leads. Every ownership claim used here was re-read in source at the
  checkpoint.
- **Executed.** One focused run, `cargo nextest run --test
  vec_push_match_binder_same_name_shadow`, reproduced ACT-1030's abort. No
  full-suite run. One-off `--run` probes (a let-wrapped and a bare tail forward)
  were blocked by host command approval and were not run. Their scratch files
  were removed.
- **Read-only fan-out.** Four read-only survey subagents covered the RC decision
  surface, design currency, the evidence tier, and filings plus the non-RC
  areas. Their claims that carry findings below were re-checked in source:
  `compile_tail_self_call`, `maybe_protect_tail_arg_alias`,
  `compile_consuming_arg_list`, `BorrowRoot`, `compute_last_uses`,
  `emit_vec_set_cow_core` and `signature_heap_category`.

---

## 3. Required capability, posture and counterfactual

**The capability, in domain terms.** Take fully typed, concrete function bodies
and produce machine code. That code computes the program's values, calls
functions and closures, loops self-tail calls in constant stack, and reports
runtime faults as recoverable panics. It must keep the heap consistent without
the programmer's involvement: it frees each value once and only once it is
unreachable, and never touches freed memory. The same code serves in-process
execution, object files for linking, and a reusable on-disk cache.

**Posture.** Phase H release compiler with one developer. It runs locally with
no deployed users. Changes are fully reversible: the cache invalidates by
schema and build identity. A working compiler delivered late costs little; a
memory-unsafe compiler shipped as a release costs a great deal.

**The smallest credible realisation (economic counterfactual only).** Separate
*deciding* ownership from *emitting* it:

- one pass over the typed body decides where references are gained and dropped;
- emission lowers those decisions mechanically;
- the decision rule is the uniform one: every use of a binder takes a
  reference and every scope end releases one;
- elision is an optimisation checked against that rule.

The project has already named this lowering as its reference semantics
(safety register §3(d)) and as option 2. In this shape the number of
"who owns this?" answers is one. A defect in it is a rule defect, visible
across the whole corpus. It is not a missing case for one syntactic shape.

---

## 4. Inventory of weight

| Layer | Measure (at `88bbbd12`) |
|---|---|
| Production source | 29,776 lines in 83 files; 10,645 comment lines; 785 sprint, FIXME and ACT references. `fn_compiler.rs` 4,824 lines including about 2,450 of inline tests; `apply.rs` 2,966 |
| Ownership decision surface | 13 distinct answers across `fn_compiler.rs`, `apply.rs`, `match_codegen.rs`, `let_if.rs`, `rc_emission.rs`, `vec_codegen.rs` and `heap.rs`. `FnCompiler` has 28 fields, 12 of them ownership state |
| Unit tests | 618 tests; 25,706 lines; `test_support.rs` 2,079 lines with about 12 entry points; about 15 file-local CLIF wrappers |
| Solution tests | 45 files touch RC or memory safety, about 303 tests. `tests/helpers/marginal.rs` 653 lines. The generator `tests/gen_ownership_flows.rs` has 60 cells × 2 toggles × 2 iteration counts |
| Golden fixtures | 19 `.clif` files, 7,938 lines, compared byte for byte. They detect change, not unsoundness (their own `MANIFEST.md`) |
| Design | `design/backend/` 9,777 lines plus the 185-line archive; crate memory 323 lines. Reading burden for a release-seam change is about 7,600 lines including cross-context authorities |
| Public API | 558 baseline lines, 351 substantive. The binary is the only consumer. About 13 of 48 top-level items have no live external consumer (§6 F11) |
| Runtime and codegen switches | 13 environment gates. `CRANELISP_CODEGEN_DUMP` is re-read on every compile; `CRANELISP_SPARK_DENSITY_TRACE` is missing from the memory's gate table |
| Open filings | FIXME 0747, 0891 (deferred), 0903, 0915 (deferred), 0929, 0931; ACT-0964, 0968, 1022, 1026, 1028, 1029, 1030, 1031 |
| Coordination | The 2026-09-30 correction sequence records 38 distinct role sessions (`sprints/archive/sprint-122.md` from "K2 attribution" to "Phase 6a entered"). The S122 evidence delta is 10,549 lines |

---

## 5. Traced paths

**Normal emission (sound, economical).** `compile_to_module` runs five phase
helpers. Each reference is one keyed fetch (`CompileContext::entry_at`) that
discriminates on the fetched arm. A miss is a located `CodegenError`. Release is
one call to the concrete type's glue (`FnCompiler::emit_typed_rc_dec` →
`DropGlueRegistry`). Nothing on this path re-derives identity.

**A value handed to a self tail call (unsound by omission).**
`compile_tail_self_call` (`compiler/apply.rs`) arms branch protection only when
the argument is syntactically `MonoExpr::If | MonoExpr::Match`. The move and
escape-borrow rules read only a bare top-level `Var` (`tail_transfer_slots`,
`protect_escaping_borrows_before_tail_jump`). Any other argument that forwards a
binding gets no reference, while the parameter flush releases the slot:

- a `let`, which is ACT-1030;
- a nested scope with no heap cleanup target (L6);
- a nullary match arm (L5, `compile_nullary_pattern` has no protect call).

The `maybe_protect_tail_arg_alias` rustdoc names this limit. The flag is also
not cleared for `let` initialisers or call arguments nested under a branch. That
contradicts the field's own documentation (`fn_compiler.rs`, the
`tail_arg_protect` field).

**A binding passed to a consuming callee.** `compile_consuming_arg_list` adds
the consuming increment only when the argument node is a `MonoExpr::Var`.
`compile_if` adds nothing to a bare-`Var` branch outside a tail argument. So
`(g (if c p q))` with a heap `p` and a consuming `g` is predicted to transfer
`p`'s only reference while scope exit also releases it. **This is a source-read
prediction.** No test covers it. Existing tests pass only literals through an
`if` (`spec_04_expressions` `(vec-len (if true [1 2 3] [4 5]))`). The same
question applies to `let` and `match` joins (`binding-indirection-consume.md`
§1 records "call args — DIRECT; patched").

**Runtime fault.** Match failure, division and `vec-get` bounds lower to
`runtime/panic(msg)` and return `0`. `vec-set` is absent from this path (§1.1).

**Cache hit.** One validation loop. Out-of-range indices become `CacheStale`
and recompile. Corrupt object bytes can still panic in the in-process linker;
that is inside the user-accepted residual.

---

## 6. Findings

Ranked by impact × likelihood × urgency. Each finding separates requirement
evidence, direct observation (source or run), inference and unknowns. Proposed
owners follow the audit contract's routing. Suspected defects go to `qa`
intake, never directly to `dev`.

### F1 — An observed use-after-free violates §12.3.1 item 2, with more predicted behind it (critical)

- **Requirement:** §12.3.1 item 2 and §12.7.8 item 4.
- **Observed:** ACT-1030's program aborts under the armed stale-release check
  at the checkpoint (§2). The mechanism is visible in source (§5). The three
  gates read argument syntax, not ownership.
- **Inference:** L2, L5, L6 and L10 each predict a use-after-free, and L4 an
  over-release, through the same "unlisted shape" gap. None is measured.
- **Unknown:** whether the fault also occurs with analysis off (F3).
- **Existing carriers:** ACT-1030, ACT-1029 and ACT-1031. ACT-1031 is deferred
  to S123 with a request for a lower model. The user's Phase-6a approval states
  that it "is not acceptance of whole-compiler memory safety".
- **Owner:** `qa` (existing intake). The design question after attribution is
  `design`(backend)'s, per ACT-1030.

### F2 — `vec-set` performs no bounds check (critical, source-read)

- **Requirement:** §12.7.2.1 names `vec-set` as a bounds panic source; §12.7.8
  item 4.
- **Observed in source:** the in-place arm of `emit_vec_set_cow_core` computes
  `data_ptr + idx*8`, loads the old element, RC-decrements it by its element
  category and stores the new value, all under `MemFlags::trusted()`. Neither
  `compile_vec_set` nor the value-position wrapper checks the index.
  `vec_set_copy` ignores an out-of-range index.
- **Inference:** an off-by-one user index on a uniquely held `Vec` reads and
  writes outside the live elements. For a heap element type it also decrements
  whatever word is there. That is a wild write, not a panic. The copy arm leaks
  the new value.
- **Coverage:** the spec row has been `[S18]` since S18, and no test calls
  `vec-set` out of range.
- **Owner:** `qa` intake with a minimal reproduction. Not previously filed.

### F3 — The standing memory-safety instruments cannot see the class that keeps failing (high)

- **Observed:**
  - **The differential oracle shares the special cases.** R9's lane compares
    analysis-on with the all-Owned lowering. Tail protection, branch forwarding
    and the flushes run in both polarities: `tail_arg_protect` is not gated on
    `ownership_analysis_off()`. So a fault in those rules is identical on both
    sides and invisible to the difference. `tests/plan/PLAN.md` already records
    that "the toggle leaves structural elisions in place".
  - **The generator does not reach this class.** `gen_ownership_flows.rs`
    arms `CRANELISP_RC_STATS` only, not `CRANELISP_RC_DEC_CHECK`. Its single
    tail position (`loop_carried`) passes a bare `x`. It excludes COW steps,
    branch or `let` tail arguments, alias shadowing and consume-position
    variety.
  - **Every S122 memory-safety defect was found incidentally:** a REPL replay,
    neighbour cells, a faulting control or review reading. The evidence delta
    says so for each one.
- **Stale record:** `tests/plan/memory-safety-coverage.md` §5 still claims
  `RC_DEC_CHECK` has zero positive assertions and that the unit tier executes no
  JIT code. Both are false now.
- **Owner:** `qa`. Evidence allocation: product axes and arming, and whether the
  oracle's reference lowering is uniform enough to discriminate this class.

### F4 — Ownership is answered 13 separate times, from syntax and names, at emission time (high, structural)

- **Observed:** thirteen distinct deciders: `value_provenance`,
  `independent_match_results`, `operand_live_binding_root`, the last-use and
  alias map, `slot_holds_frame_owned_reference`, `tco_slot_disposition`, the
  consuming claims, `scrutinee_lifetime_for_arm`, `has_cleanup_targets` in
  `protect_return_value`, the `pop_scope_with_cleanup` skip, the `Var`-syntax
  consume gates, `tail_arg_protect` with `maybe_protect_tail_arg_alias`, and
  `protect_escaping_borrows_before_tail_jump`. They form two partly overlapping
  families, expression provenance and slot ownership. There is no single
  per-expression fact.
- **Two observed disagreements:**
  - ACT-1026: `value_provenance` reads a forwarding join as `NotOwnedHere`
    while the join transfers its binder.
  - For an `if` over bindings, `value_provenance` answers `NotOwnedHere` while
    `operand_live_binding_root` and the `Var`-syntax gates treat it as an owned
    temporary.
- **Name-keyed residue against the S121 binder-slot rule** (`binding-scope.md`;
  the crate memory's "ONE SLOT PER BINDER, never per name"):
  - `BorrowRoot::Binding(Symbol)` is re-resolved by name at the jump;
  - `compute_last_uses` and `register_alias` use `HashMap<Symbol, …>` and are
    never scoped (ACT-1029);
  - promotion is read through `tco_owned_params` by name
    (`pop_scope_with_cleanup`, L3);
  - `tail_bare_var_names` and `tail_arg_supersedes_param` compare names;
  - `return_cow_source_in_scope` tests name membership.
  - Consuming claims are keyed by `MonoExpr` pointer address. That is correct
    only while no pass clones nodes; the design records it as asserted.
- **History (Git and archive):** each of 0810, 0917, IOR-5, ACT-0974, ACT-1021,
  ACT-1024 and ACT-1027 added or corrected one of these answers. S122's
  corrections were locally sound and removed code (`vec_codegen.rs` lost its
  retain-reconciliation machinery). They did not reduce the number of answers.
- **Design realisation:** `binding-indirection-consume.md` §1 ruled in S114
  that "every consume position keys its accounting off this ONE function".
  `compile_consuming_arg_list` and `element_consuming_inc` still key on
  `MonoExpr::Var`. W-B5, the fn-return convergence, was retired on the grounds
  that "the three finders answer different questions".
- **The decision that addresses this already exists and has lapsed.** The S119
  record (`sprints/archive/sprint-119.md`, "Option 2 deferral") called option 2
  "prophylactic against future special-case defects, not curative of the
  present baseline", scheduled its measurement report-only and deferred
  adoption to "S120, on the number". S120, S121 and the roadmap never mention it.
  PLAN.md records "no sprint schedules the measurement". S122's defects are the
  future special-case defects that deferral was hedging against.
- **Owner:** `sprint`, to put the lapsed option-2 decision and its measurement
  to the user before ACT-1031 resumes instance repair. `arch` owns the option
  paper; `design`(backend) owns the stratum's interior. This audit does not
  recommend an answer.

### F5 — The non-concrete RC licence remains, and nothing measures its exposure (medium)

- **Observed:** `signature_heap_category`'s `Err(_) ⇒ HeapCategory::Mixed` and
  the type-keyed shallow-dec arm in `emit_heap_binding_decs` are both present.
  The S119 census found 3,646 bare-`Var` licences and a reproduced SIGSEGV for
  accessor face F1 at payload ≥ 1024 (`non-concrete-release-contract.md` §2.4).
- **Since then:** the typecheck producer obligations landed (accessor A-MINT;
  trait-method instances, whose 0916 guard is now GREEN). Whether any production
  frame still reaches the arm is **unknown**. The §7.3 census that would answer
  it was never built.
- **Stale claims:** the crate memory and the rustdoc still assert that
  "families 2 and 3 … leak today". Neither is current evidence either way.
- **Existing carriers:** FIXME 0903, 0929 and 0931; contract §7.2–§7.4. FIXME
  0891 has been deferred on 0903 since S119.
- **Owner:** `design`(backend).

### F6 — Standing design documents decay as a block (medium)

- **Observed:**
  - **Status went stale in one commit.** Eleven "working tree, uncommitted, not
    accepted" status claims across seven documents became false at the
    checkpoint commit: `backend.md` §8, `s122-closure.md`, `ownership-codegen.md`
    §0 / §13.3 / §13.7, `transitive-drop-glue.md` §5, `non-concrete-release-contract.md`
    §7 / §7.6 and `ring2-rc.md` §3.3.
  - **Sampled claims.** About 45 source claims were sampled; 15 are stale or
    false. Examples: the non-existent `compile_consuming_arg_list_moded`;
    "`LinkerConfig`" (16 mentions); `binding-indirection-consume.md`'s pointer
    to an `ownership-codegen.md` §13.7 "SUPERSEDED banner" that no longer exists; the "TARGET design"
    label on implemented `executable-generation.md` §12.
  - **History in the standing tree.** Three sprint-named records
    (`s115-carrier-and-rc-sweep.md`, `s117-failed-member-attribution.md`,
    `s122-closure.md`) and three work orders (`binding-indirection-consume.md`
    §5, `io-scheduling.md`, `io-trampoline.md` §12–§17, about 2,000 of its
    2,279 lines) sit there. That contradicts `design/backend/CLAUDE.md` ("executed
    plans … are Git's job").
  - **Duplicated authority.** At least 10 rule families are stated in two to
    four homes: the COW rule of `ownership-codegen.md` §13.7, the TCO verdict, IOR-5, the entry
    convention, the nullary guard, glue construction, failed-member atomicity
    and others.
  - **The checker cannot see it.** `check_documents.py` reports zero findings in
    this scope. It checks reference and symbol existence, not prose.
- **Owner:** `design`(backend).

### F7 — The crate memory carries false claims and restates design (medium)

- **Observed in `crates/cranelisp-backend/CLAUDE.md`:**
  - "Three RC decisions" introduces a 13-row table;
  - `got_data_symbol_name` is called "non-injective … FIXME 0748". FIXME 0748
    was deleted in S119 and the scheme escapes `_`; the stale text also sits in
    the `resolution.rs` rustdoc;
  - `CACHE_FORMAT_VERSION` and `CACHE_SCHEMA_VERSION` are called "independent",
    but `cache/mod.rs` aliases one to the other;
  - it cites "monotone `SymbolTable::next_got_slot`", a field that no longer
    exists;
  - it calls `heap.rs` the sole layout importer, but `drop_glue.rs` and
    `rc_emission.rs` use `HeapHeader` directly;
  - it places `HeapAdt`, `HeapClosure` and `HeapVec` in `cranelisp-types`, but
    they are backend items;
  - the seam map omits `dependent_spark.rs`, `io_nodes.rs`, two crate-root test
    files and one environment gate.
- **Also:** its 13-row predicate table restates at least six design homes.
  `Cargo.toml` still cites the retired `facades/backend.md`, contradicting
  ACT-0964 item 3's "complete".
- **Owner:** `dev`(backend) for the memory. `arch` for the types memory's
  agreement.

### F8 — Source commentary is a second, decaying history (medium)

- **Observed:**
  - 36% of production lines are comments, about 50% in `fn_compiler.rs`'s
    production region.
  - The `CACHE_SCHEMA_VERSION` rustdoc (`cache/mod.rs`) is a version changelog
    of roughly 300 lines.
  - Rustdoc is spliced onto the wrong items: `flush_let_scopes_before_tail_jump`'s
    on `request_capture_glue`; `body_has_self_call`'s gate-3 on the test-only
    `is_fresh_construction`, which is also listed as a production consumer;
    the same splice on `cow_source_ownership`.
  - `match_codegen.rs` calls a five-point lattice "three-point".
  - `heap.rs` says its layout items are `pub` for intrinsics, which cannot
    depend on the backend. Intrinsics keeps its own copy, e.g.
    `CLOSURE_DROP_GLUE_OFFSET`, so the closure, ADT and Vec layouts have two
    sources.
  - Dead mechanisms are kept "probe-reachable" (`_atomicity` on consuming
    increments).
- **Strength:** the invariant comments that carry a falsifier earn their place.
  Examples: claim-set "asserted, not structural"; "row 2 must stay `Replace`".
- **Owner:** `dev`(backend). The layout dual source goes to `arch` (a
  boundary question).

### F9 — Spec §12.1 "current reference representation" is inaccurate (medium, other owner)

- **Observed:** every heap layout in §12.1.2–§12.1.5 omits the 16-byte
  `HeapHeader` (`alloc_size`, `rc`). String length is at 16, not 0. The ADT tag
  is at 16. Vec fields start at 16. The closure has a `drop_glue_ptr` at 24 and
  its captures start at 32. The section also omits value flattening and stack
  placement.
- **Why it matters:** the section declares itself "descriptive of the current
  backend choice", so it is a false current-state claim, not a normative
  constraint.
- **Owner:** `spec`, which frames the correction for the user.

### F10 — Evidence records misattribute (low)

- **Observed:**
  - `tests/vec_push_match_binder_same_name_shadow.rs` carries `// defect:
    class=binder-name-underkey locus=crates/cranelisp-backend/src/heap.rs::register_alias`. It fails in its
    control, for ACT-1030's reason, and never runs the subject.
  - The committed ACT-0974, 1021, 1024 and 1027 cells lack their owed `fixed=`
    stamps, so `grep -L fixed=` lists green guards as open.
  - The intrinsics detector names a stale mechanism in its abort text ("FIXME
    0494 bug #2 — … launched-strand teardown").
- **Owner:** `qa`, with `test`. The detector text belongs to
  `design`(intrinsics) through `qa`.

### F11 — Public and carried surface without consumers (low)

- **Observed:**
  - `load_object`, `LinkerArtefact` and `ObjectArtefact` have no caller.
  - The cache write-packet family is consumed only by the dormant
    `src/cache_writer.rs`.
  - `CompileContext`'s public fields, `primitives_inline` (exports nothing),
    `HeapClosure`, `NULLARY_THRESHOLD_I64`, `jit_free_memory_call_count`,
    `got_observer::emit`, `serialise_meta`/`deserialise_meta` and
    `CACHE_FORMAT_VERSION` have no live external consumer.
  - `Realization::ExternShim { borrowed_sibling }` is carrier-only
    (`ownership-codegen.md` §0, §9). ACT-0974 made every shim consume, so no
    producer can populate it. It still costs a cache validation arm and tests.
- **Inference:** about 25–30% of top-level public items are unsupported current
  weight.
- **Owner:** `arch` (public surface and the types carrier; the user gates any
  change).

### F12 — Prior residue still undisposed (low, process)

- **ACT-0964:** items 1 and 2 are open. Both soft arms are present. A third
  silent arm exists: `constructor_metas` returns empty for a missing module
  table, and `concrete_field_types` returns the unsubstituted declared fields.
  Item 3's "complete" is contradicted by `Cargo.toml`.
- **ACT-0969, backend row:** re-judged here. `fn_compiler.rs` fell from 5,202 to
  4,824 lines and `apply.rs` from 3,014 to 2,966; `compile_apply` is 233 lines.
  File size alone is not the issue; F4 is. `sprint` may strike the row.
- **`FnCompiler` field count:** `backend.md` §3 says "No filing carries it". It
  is still unrouted; F4 subsumes it.
- **Owner:** `sprint` (disposition); `design`(backend) (ACT-0964).

---

## 7. Strengths

- **Structural boundary.** Keyed consumption survives a large sprint intact:
  no resolver, and loud located misses on the call and value seams, each with a
  proven negative.
- **`EntryConvention`.** Derived once from the lifecycle arm, exhaustive, and
  typed so that an adaptation against a declared extern mode cannot be
  written. It is the model for converging a decision.
- **`DropGlueRegistry`.** One construction authority, declaration-first
  construction for recursive types, no depth bound, and a `finish()` fence.
- **Nullary skip guard.** One body with a control-flow polarity pin; the
  design notes that counting constants would not pin it.
- **Cache trust boundary.** One validation loop with a planted-corruption cell
  per class. The GOT allocator is fallible.
- **Honest grading vocabulary.** Documents say "asserted, with falsifier" where
  that is the truth.
- **Evidence tooling.** `MarginalPair` has its own capability fence, and the
  generator plants its own faults. Both are sound instruments. They are pointed
  at too few axes (F3).
- **S122 simplified as it fixed.** The ACT-1024 change deleted the recorded
  retain and reconciliation machinery rather than adding another layer.

---

## 8. Recommendations

**Pending disposition.** Cost classes: S is less than one role session; M is
one wave; L is multiple waves or a user decision with re-sequencing.

| # | Recommendation | Evidence | Cost | Proposed owner |
|---|---|---|---|---|
| R1 | Put the lapsed option-2 decision (uniform dev-tier RC emission, elision moved behind the differential guard) to the user at S123 Phase 1. Take its measurement (PLAN.md's recorded method, including the structural elisions the toggle leaves in place) **before** ACT-1031 resumes instance repair, so the repair's shape is chosen once | F1, F3, F4 | M to measure; L if adopted | `sprint`, then `arch` and `design`(backend) |
| R2 | Intake `vec-set`'s missing bounds check with a minimal reproduction and a discriminating control | F2 | S | `qa`, then `test` |
| R3 | Measure the unmeasured predictions in one batch, armed with `CRANELISP_RC_DEC_CHECK`, with halves observed separately: an `if`, `let` or `match` over bindings at a consuming argument; L2, L4, L5, L6, L9 and L10; a shadowed borrow root | F1, F4 | M | `qa`, then `test` |
| R4 | Re-allocate memory-safety evidence to the failing axes: arm the generator's stale-release check; add tail-argument shape, COW step, alias shadowing and consume position as product axes; state what the differential oracle cannot discriminate while the toggle shares the special cases | F3 | M | `qa` |
| R5 | Sweep backend design status and retire the history: correct the eleven status claims; extract, then delete, the sprint records and executed work orders; reduce `io-trampoline.md` to its mechanism; give each RC rule one home and cite it from the rest | F6 | M | `design`(backend) |
| R6 | Repair the crate memory's false claims and restated design. Move the schema changelog and history narration to Git; fix the spliced rustdoc | F7, F8 | S–M | `dev`(backend) |
| R7 | State the actual extent of the binder-slot rule, or converge the name-keyed residue. ACT-1029 carries only the alias map | F4 | M | `design`(backend), with `qa` measurement first |
| R8 | Build or re-scope the §7.3 non-concrete census so that R17's exposure is known. Delete or confirm the "leak today" claims | F5 | M | `design`(backend) |
| R9 | Correct spec §12.1's descriptive layouts | F9 | S | `spec` (user-approved wording) |
| R10 | Dispose the public items with no consumer and the carrier-only `borrowed_sibling`; decide the layout dual source | F8, F11 | S–M | `arch` (user API gate) |
| R11 | Repair the guard's `// defect:` attribution and the owed `fixed=` stamps; refresh `memory-safety-coverage.md` §5 | F10 | S | `qa`, `test` |
| R12 | Dispose ACT-0964 items 1–2 and strike ACT-0969's backend row | F12 | S | `sprint`, `design`(backend) |

**Deferred extension, not present work.** Cache-object relocation offsets can
panic on a malformed `.o` (`cache/linker.rs`). The user accepted corrupt-cache
risk on 2026-09-24.

- **Trigger to reconsider:** a compiler-written cache observed to produce a
  truncated object.
- **Evidence needed:** that observation.
- **Least costly response:** a bounds-checked read that returns `CacheStale`.
- **Also:** the crate memory's "every arm diagnoses and recompiles" overstates
  that posture. Narrowing the claim is part of R6.

---

## 9. Disposition trail

| Recommendation | Decision | Date | Carrier |
|---|---|---|---|
| R1–R12 | pending | — | — |

*Record each decision here at S123 Phase 1: accepted, with the resulting filing
or owning-document change; or declined, with the rationale. Preserve any
unaddressed point in its canonical carrier before this file is retired.*
