# LOC Pre-Pass — Sprint 87 Stage B (Wave 1a)

> **What this is.** The quantitative `tokei`-driven LOC table that *opens* Stage B
> and **feeds every per-crate audit pass**. It is the leading-indicator map of where
> the per-crate qualitative passes should look hardest. Authored by `/review` per
> `sprints/SPRINT.md` → Stage B "Quantitative pre-pass" (R5c three-column protocol).
>
> **Read this caveat first.** LOC is a *leading* indicator, not a verdict. Size
> correlates with duplication / mixed-concern / inefficiency risk — it does **not**
> measure defects. A 1,966-line module that is one well-factored dispatch table is
> healthier than a 300-line module with three copy-pasted heap-classification paths.
> This table tells the audit *where to start*, not *what is wrong*.

**Instruments.** `tokei` v14.0.0 (`Rust` `code` field, i.e. non-blank, non-comment
source lines) for raw LOC. Inline-test LOC estimated two ways and summed:
(1) brace-tracked code-lines inside `#[cfg(test)]` blocks within a production file;
(2) **sibling test files** — files whose basename is `tests.rs`, `test_support.rs`,
or `*_tests.rs`, included via `#[cfg(test)] mod tests;` — counted **wholly** as
inline-test (their corrected production LOC is 0). `tests/`-dir LOC measured with
`tokei` on each surface's external `tests/` directory.

**The three-column protocol (R5c).** File-level tools cannot split inline test
modules from production code, so each row carries: **raw** (tokei code) /
**inline-test** (estimate) / **corrected** = raw − inline-test. **Ranking is driven
by corrected non-test LOC**, never raw — uncorrected LOC badly mis-ranks the big
crates (see the typecheck surprise below).

---

## 1. Per-crate summary (ranked by corrected non-test LOC)

| # | Surface | Raw code | Inline-test est. | **Corrected (prod)** | External `tests/`-dir |
|---|---|--:|--:|--:|--:|
| 1 | **`src/`** (root package) | 20,406 | 6,767 | **13,639** | 19,011 |
| 2 | **`cranelisp-backend`** | 17,555 | 8,068 | **9,487** | 19 |
| 3 | **`cranelisp-typecheck`** | 21,180 | 14,304 | **6,876** | 0 |
| 4 | **`cranelisp-frontend`** | 6,505 | 3,128 | **3,377** | 0 |
| 5 | **`cranelisp-types`** | 4,781 | 1,746 | **3,035** | 0 |
| 6 | **`cranelisp-intrinsics`** | 5,033 | 2,968 | **2,065** | 0 |
| 7 | **`cranelisp-platform`** | 2,076 | 761 | **1,315** | 583 |
| 8 | **`cranelisp-primitives`** | 1,849 | 893 | **956** | 0 |
| — | `cranelisp-exe-bundle` | 28 | 0 | **28** | 0 |
| | **Total (8 surfaces + bundle)** | 79,413 | 38,635 | **40,778** | 38,624 |

> `cranelisp-exe-bundle` (65-line crate per the R1 table; 28 LOC of actual Rust
> `code` excluding comments/blanks) is folded into the `src/` *audit surface* but
> reported on its own row so the figure is legible. The repo-level `tests/` directory
> (19,011 LOC of free-standing integration tests) attaches to the `src/` surface.

**The headline rerank.** The rough baseline cited `typecheck (~31k)`, `src/ (~32k)`,
`backend (~27k)` (those were uncorrected, whole-crate-including-deps figures). On the
**corrected** axis the order is **`src/` > `backend` > `typecheck`** — and the gap is
large: typecheck's 21,180 raw LOC is **68% inline test** (14,304), collapsing it from
apparent #1 to actual #3. This is exactly the mis-ranking R5c was written to prevent.

---

## 2. Per-module breakdown (ranked by corrected non-test LOC within each crate)

### `src/` — corrected 13,639 (deep-scrutiny surface #1)

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `process_form.rs` | 2134 | 369 | **1765** |
| `repl.rs` | 1994 | 349 | **1645** |
| `session_v4.rs` | 2235 | 807 | **1428** |
| `scheduler.rs` | 1493 | 446 | **1047** |
| `bootstrap.rs` | 956 | 191 | 765 |
| `worker.rs` | 1842 | 1093 | 749 |
| `exe.rs` | 760 | 202 | 558 |
| `display.rs` | 755 | 245 | 510 |
| `pretty.rs` | 514 | 78 | 436 |
| `platform.rs` | 783 | 380 | 403 |
| `save.rs` | 550 | 151 | 399 |
| `expander.rs` | 631 | 238 | 393 |
| `bind_chain_analysis.rs` | 746 | 361 | 385 |
| `main.rs` | 402 | 50 | 352 |
| `eval.rs` | 343 | 0 | 343 |
| `imports.rs` | 645 | 314 | 331 |
| `observability.rs` | 864 | 546 | 318 |
| `io_trace.rs` | 419 | 113 | 306 |
| `got_trace.rs` | 233 | 18 | 215 |
| `session_setup.rs` | 335 | 134 | 201 |
| (24 more modules, each corrected ≤ 137) | | | |

Genuinely-large production modules (low inline-test share): `process_form.rs`,
`repl.rs`, `scheduler.rs`, `bootstrap.rs`, `eval.rs`. `worker.rs` (1842 raw) is
heavily test-laden (59% inline test) — its corrected 749 is mid-pack, not top. The
top-4 (`process_form`, `repl`, `session_v4`, `scheduler`) are the pipeline-
orchestration core — expected to be large, but the largest single-file targets for
mixed-concern scrutiny.

### `cranelisp-backend` — corrected 9,487 (deep-scrutiny surface #2)

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `compiler/control_flow.rs` | 1673 | 210 | **1463** |
| `compiler/mod.rs` | 1577 | 298 | **1279** |
| `compiler/vec_codegen.rs` | 1132 | 106 | **1026** |
| `compiler/trace_codegen.rs` | 1119 | 417 | 702 |
| `lib.rs` | 4849 | 4202 | 647 |
| `compiler/apply.rs` | 649 | 74 | 575 |
| `cache/linker.rs` | 724 | 210 | 514 |
| `jit.rs` | 1121 | 657 | 464 |
| `compiler/match_codegen.rs` | 414 | 0 | 414 |
| `heap.rs` | 690 | 296 | 394 |
| `schema.rs` | 517 | 182 | 335 |
| `compiler/literals.rs` | 270 | 0 | 270 |
| `compiler/primitives_inline.rs` | 209 | 0 | 209 |
| `cache/serialize.rs` | 509 | 274 | 235 |
| `cache/object.rs` | 548 | 355 | 193 |
| `cache/manifest.rs` | 433 | 241 | 192 |
| `cache/mod.rs` | 404 | 274 | 130 |
| (rest each corrected ≤ 130) | | | |

**`lib.rs` is the headline correction here:** 4,849 raw — by far the largest single
file in the workspace — but **87% inline test** (4,202), corrected 647. It is *not* a
4.8k-line god module; it is a modest production surface with a giant inline test
block. The real deep-scrutiny targets are the three big `compiler/` modules
(`control_flow`, `mod`, `vec_codegen`), all with *low* inline-test share — genuinely
large production code, and the canonical place to watch for the
`sketch/audits/codegen.md` HIGH-severity patterns (duplicate heap-classification,
ISA-built-ad-hoc, panics in non-test paths).

### `cranelisp-typecheck` — corrected 6,876 (deep-scrutiny surface #3)

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `program.rs` | 2094 | 128 | **1966** |
| `traits.rs` | 1731 | 13 | **1718** |
| `checker.rs` | 1160 | 65 | **1095** |
| `infer.rs` | 787 | 2 | **785** |
| `adt.rs` | 1556 | 1042 | 514 |
| `form.rs` | 886 | 643 | 243 |
| `unify.rs` | 318 | 147 | 171 |
| `cluster.rs` | 230 | 111 | 119 |
| `resolve.rs` | 433 | 315 | 118 |
| `scope.rs` | 122 | 62 | 60 |
| `result.rs` | 36 | 0 | 36 |
| `builtins.rs` | 1747 | 1746 | **1** |
| `program/tests.rs` *(sibling test file)* | 4935 | 4935 | 0 |
| `infer/tests.rs` *(sibling test file)* | 2183 | 2183 | 0 |
| `checker/tests.rs` *(sibling test file)* | 1221 | 1221 | 0 |
| `traits/tests.rs` *(sibling test file)* | 952 | 952 | 0 |
| `checker/test_support.rs` *(sibling test file)* | 494 | 494 | 0 |
| `traits/primitive_dispatch_tests.rs` *(sibling)* | 73 | 73 | 0 |

This crate has the workspace's most aggressive test/prod split. **Two distinct
test-stripping effects:**
- **Sibling test files** — `program/tests.rs` (4,935!), `infer/tests.rs` (2,183),
  `checker/tests.rs` (1,221), `traits/tests.rs` (952), `checker/test_support.rs`
  (494), `traits/primitive_dispatch_tests.rs` (73). These are pure test code included
  via `#[cfg(test)] mod tests;` — zero production LOC.
- **`builtins.rs`** — 1,747 raw, corrected **1**. Its own doc comment declares it is
  entirely `#[cfg(test)]` typecheck test-support fixtures. Not a production module.

The genuine production heavies are `program.rs` (1,966, only 6% inline test),
`traits.rs` (1,718, ~1% inline test — almost pure production), `checker.rs` (1,095),
`infer.rs` (785, ~0% inline test). These four are where the typecheck audit looks
hardest, and they are the canonical home for the `sketch/audits/typechecker.md`
debts (scheme handling, inference). `adt.rs` looks large at 1,556 raw but is 67%
inline test (corrected 514).

### `cranelisp-frontend` — corrected 3,377

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `ast_builder.rs` | 3041 | 1830 | **1211** |
| `reader.rs` | 1694 | 585 | **1109** |
| `defmacro.rs` | 641 | 220 | 421 |
| `module_extract.rs` | 651 | 314 | 337 |
| `quasiquote.rs` | 456 | 179 | 277 |
| `lib.rs` | 22 | 0 | 22 |

`ast_builder.rs` is the crate's largest file at 3,041 raw but 60% inline test
(corrected 1,211). `reader.rs` (1,109 corrected, 35% inline test) is the more
production-dense of the two. Both are top-of-crate scrutiny targets.

### `cranelisp-types` — corrected 3,035

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `module.rs` | 1537 | 852 | **685** |
| `ast.rs` | 424 | 0 | 424 |
| `resolve.rs` | 488 | 169 | 319 |
| `types.rs` | 502 | 213 | 289 |
| `error.rs` | 323 | 46 | 277 |
| `mono_expr.rs` | 458 | 199 | 259 |
| `newtype.rs` | 150 | 0 | 150 |
| `sexp.rs` | 144 | 0 | 144 |
| (rest each corrected ≤ 72; `test_support.rs` is a sibling test file, 0) | | | |

Interface-types crate (`/arch`-only). `module.rs` is the one notable concentration
(685 corrected; 55% inline test). Otherwise broadly distributed — consistent with a
DTO/interface crate.

### `cranelisp-intrinsics` — corrected 2,065

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `trace.rs` | 924 | 515 | **409** |
| `io.rs` | 791 | 456 | **335** |
| `drop.rs` | 633 | 448 | 185 |
| `vec_runtime.rs` | 446 | 264 | 182 |
| `trace_format.rs` | 448 | 274 | 174 |
| `panic.rs` | 427 | 273 | 154 |
| `alloc.rs` | 256 | 124 | 132 |
| `ivar.rs` | 292 | 171 | 121 |
| (rest each corrected ≤ 92) | | | |

Runtime-intrinsics crate — **59% inline test crate-wide**, the highest test density
of any surface. No single production heavy; `trace.rs` and `io.rs` top out around
335–409 corrected. This is the crate most likely to carry `unsafe` (alloc, drop, rc,
raw pointers) — the per-crate pass should run the §Unsafe code audit here regardless
of size.

### `cranelisp-platform` — corrected 1,315

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `lib.rs` | 1057 | 578 | **479** |
| `schema.rs` | 532 | 88 | **444** |
| `declare.rs` | 211 | 0 | 211 |
| `adt.rs` | 276 | 95 | 181 |

Plus a 583-LOC external `tests/` dir. Small crate; `lib.rs` and `schema.rs` are the
two production concentrations.

### `cranelisp-primitives` — corrected 956

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `operator.rs` | 437 | 165 | **272** |
| `string.rs` | 280 | 93 | 187 |
| `marshal.rs` | 258 | 82 | 176 |
| `lib.rs` | 472 | 307 | 165 |
| `ring0.rs` | 166 | 59 | 107 |
| (rest each corrected ≤ 27) | | | |

Smallest non-trivial surface. Nothing large; the per-crate pass is quick here.

### `cranelisp-exe-bundle` — corrected 28

| module | raw | inline-test | corrected |
|---|--:|--:|--:|
| `lib.rs` | 28 | 0 | 28 |

Trivial. Folded into the `src/` audit surface.

---

## 3. Deep-scrutiny priority list (top 15 modules across all surfaces, by corrected LOC)

The per-crate passes look hardest at these first. **Size is a leading indicator, not
a verdict** — a large well-factored module passes; the list says only *where to spend
the first hour*.

| # | Module | Corrected | Raw | Inline-test | Note |
|---|---|--:|--:|--:|---|
| 1 | `cranelisp-typecheck/program.rs` | 1966 | 2094 | 128 | program-level inference, ~6% test — genuinely large prod |
| 2 | `src/process_form.rs` | 1765 | 2134 | 369 | per-form pipeline orchestration |
| 3 | `cranelisp-typecheck/traits.rs` | 1718 | 1731 | 13 | almost pure production (~1% test) — trait resolution |
| 4 | `src/repl.rs` | 1645 | 1994 | 349 | REPL session loop |
| 5 | `cranelisp-backend/compiler/control_flow.rs` | 1463 | 1673 | 210 | codegen — watch heap-classification dup |
| 6 | `src/session_v4.rs` | 1428 | 2235 | 807 | unified session — 36% test |
| 7 | `cranelisp-backend/compiler/mod.rs` | 1279 | 1577 | 298 | codegen core |
| 8 | `cranelisp-frontend/ast_builder.rs` | 1211 | 3041 | 1830 | largest raw file in frontend; 60% test |
| 9 | `cranelisp-frontend/reader.rs` | 1109 | 1694 | 585 | s-expr reader |
| 10 | `cranelisp-typecheck/checker.rs` | 1095 | 1160 | 65 | check driver, ~6% test |
| 11 | `src/scheduler.rs` | 1047 | 1493 | 446 | scheduler-driven pipeline |
| 12 | `cranelisp-backend/compiler/vec_codegen.rs` | 1026 | 1132 | 106 | vec codegen, low test share |
| 13 | `cranelisp-typecheck/infer.rs` | 785 | 787 | 2 | Algorithm-W core, ~0% test |
| 14 | `src/bootstrap.rs` | 765 | 956 | 191 | prelude/bootstrap loading |
| 15 | `cranelisp-backend/compiler/trace_codegen.rs` | 702 | 1119 | 417 | trace codegen, 37% test |

**Density flag (low inline-test share = densest production code, hardest to audit by
eye):** `traits.rs` (~1%), `infer.rs` (~0%), `program.rs` (~6%), `checker.rs` (~6%),
`vec_codegen.rs` (~9%) — these five carry the most uninterrupted production logic per
file and warrant the closest read.

---

## 4. Surprises surfaced for the per-crate passes

1. **Typecheck is not the biggest crate — it's third.** 68% of its 21k raw LOC is
   test (sibling `*/tests.rs` files + an entirely-test `builtins.rs`). Anyone
   budgeting audit effort off the rough `~31k` baseline would over-allocate to
   typecheck by ~3×. Corrected: `src/` (13.6k) > `backend` (9.5k) > `typecheck`
   (6.9k).

2. **`cranelisp-backend/lib.rs` is the largest raw file in the workspace (4,849) but
   87% inline test.** Corrected 647. Not a god module — do not flag it on size alone;
   read the corrected figure.

3. **`cranelisp-typecheck/builtins.rs` (1,747 raw) is 100% test-support** by its own
   doc comment — corrected 1. A naive raw-LOC ranking would put it in the top 10
   production modules; it has zero production code.

4. **`cranelisp-intrinsics` is the highest test-density surface (59% inline test).**
   Its production modules are all small (≤409 corrected), but it is the most likely
   `unsafe`-bearing crate (alloc/drop/rc/raw-pointer runtime) — the per-crate pass
   should run the unsafe-code audit there irrespective of LOC.

5. **The four densest production typecheck modules (`traits`, `infer`, `program`,
   `checker`) carry near-zero inline tests** — their tests live in the sibling
   `*/tests.rs` files. High production density + large size = the workspace's hardest
   read-by-eye region.
