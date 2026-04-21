# Examples `--run` Path Remediation

**Owner**: `/stdlib` (primary); `/examples` validates at Phase 5b
**Sprint**: 60, Workstream F
**Status**: Decision record — implementation pending
**Triggering condition**: `/arch` Sprint-60 review Condition 4 — "The prelude-expose-vs-examples-rewrite co-decision MUST be recorded in a design doc. Verbal / in-session decision is insufficient — the decision shape sets a precedent for 'what belongs in the prelude' that future stdlib work will cite."

Related docs:

- `stdlib/plan-stdlib.md` §4 (Prelude) — the normative prelude-philosophy reference. Line 297 explicitly whitelists a short list of primitives for prelude re-export (`bind`, `vec-len`, `vec-get`, `vec-set`, `vec-push`, `parse-int`, `str-concat`, `str-eq`).
- Root `CLAUDE.md` §Design Principles — "Optional prelude" and "Stdlib separation" principles.
- `tests/CLAUDE.md` §Test Prelude Fixture — describes the `tests/fixtures/preamble_primitives.cl` harness path that currently masks the gap.

---

## §1 Problem

### 1.1 The gap

Ring 4 acceptance criterion: `cargo run -- --run examples/FOO.cl` must succeed for every `.cl` in `examples/`. **Actual state: 27 of 27 fail.** Confirmed by running `cargo run -- --run examples/01-integers.cl`:

```
error: module error at 0..0: module '01-integers' failed:
  type error at 350..357: undefined variable: add-i64
```

The failure surfaces at the very first primitive reference — the gap is systemic, not example-specific.

### 1.2 Why `tests/examples.rs` is green

Every example-running test in `tests/examples.rs` calls `compile_and_run_simple(&source)` (tests/examples.rs:17). That helper defaults to injecting **`tests/fixtures/preamble_primitives.cl`** as a preamble (tests/helpers/mod.rs:508–509), whose entire content is:

```clojure
(import [primitives [*]])
```

This single-line fixture glob-imports every Ring-0/1 primitive with bare names into the test module. `cargo run -- --run ...` does **not** inject this preamble — it loads only the stdlib prelude (`stdlib/prelude.cl`), which is a pure re-export shell for **trait-wrapped operators and domain types** and exposes no bare primitive names at all. Green tests + red `--run` is therefore not a compiler bug; it is a **test-harness lie**: the tests exercise a different name surface from the one `--run` presents to the user.

### 1.3 Enumeration of distinct bare primitives used across the 27 `.cl` files

Grepped via ripgrep over `examples/**/*.cl` (cache artefacts excluded). 30 distinct bare primitive names, grouped by family:

| Family | Primitives | Example file count |
|---|---|---|
| Int arithmetic | `add-i64`, `sub-i64`, `mul-i64`, `div-i64` | ~27 (near-universal) |
| Int comparison | `eq-i64`, `lt-i64`, `gt-i64`, `le-i64`, `ge-i64` | ~20 |
| Float arithmetic | `add-f64`, `sub-f64`, `mul-f64`, `div-f64` | 4–6 |
| Float comparison | `eq-f64`, `lt-f64`, `gt-f64`, `le-f64`, `ge-f64` | 4–6 |
| Bool | `not`, `eq-bool` | ~10 |
| String | `str-concat`, `str-eq`, `str-len`, `char-at`, `int-to-string`, `float-to-string`, `bool-to-string` | ~8 |
| Vec | `vec-len`, `vec-get`, `vec-set`, `vec-push` | 2–4 |

IO primitives (`print`, `read-line`) are imported explicitly from `platform.stdio` in the IO examples and are therefore **not** part of this gap. The gap is purely in the Ring-0/1 inline and extern primitive surface.

Raw call-site totals (sampled via grep; top 10): `add-i64` 798, `sub-i64` 177, `mul-i64` 141, `str-concat` 140, `str-len` 123, `str-eq` 120, `not` 117, `eq-i64` 116, `lt-i64` 100, `int-to-string` 98. These numbers confirm that the shape of the gap is "first-class arithmetic / comparison / string" — the primitives the examples use to *teach the language surface ring by ring*.

### 1.4 A note on the 4-line prelude parity lesson

Sprint 59 Wave 1 demonstrated that cross-path divergence between the test harness and `--run` is how load-bearing defects slip through. The test-fixture preamble documented in §1.2 is exactly that shape, applied to the examples surface: the tests validate a source file that would never compile under the normative `--run` entry point. This doc proposes a resolution that eliminates the divergence at its source rather than papering over it.

---

## §2 Options

### Option A — Expose bare primitives through the stdlib prelude

**Shape**: Add an `(export [primitives [...]])` clause to `stdlib/prelude.cl` re-exporting the 30 primitive names enumerated in §1.3.

**Exhaustive list** (30 names; groups as in §1.3):

```clojure
;; Int arithmetic + comparison + Bool
(export [primitives [add-i64 sub-i64 mul-i64 div-i64
                     eq-i64 lt-i64 gt-i64 le-i64 ge-i64
                     not eq-bool]])
;; Float arithmetic + comparison
(export [primitives [add-f64 sub-f64 mul-f64 div-f64
                     eq-f64 lt-f64 gt-f64 le-f64 ge-f64]])
;; String
(export [primitives [str-concat str-eq str-len char-at
                     int-to-string float-to-string bool-to-string]])
;; Vec
(export [primitives [vec-len vec-get vec-set vec-push]])
```

**Consistency with the "Optional prelude" principle (root CLAUDE.md)**: The principle says *nothing in the prelude is required for the language to work* — an empty prelude is a valid starting point, and the prelude provides *convenience* (traits, operators, types, macros). This is a principle about minimality floor (the prelude must not be load-bearing for compilation), not a principle about ceiling (what convenience is permitted). Exposing primitive names is convenience of exactly the same shape as exposing `+` through the Num trait: a stable name a user expects to be in scope when they type into the REPL.

**Consistency with `plan-stdlib.md §4`**: The plan already specifies (line 297) that a short list of primitives is re-exported through prelude: `bind`, `vec-len`, `vec-get`, `vec-set`, `vec-push`, `parse-int`, `str-concat`, `str-eq`. Option A is therefore a **quantitative extension** of an already-sanctioned qualitative category ("some primitives belong in the prelude") — not a new category.

**Collision risk**: Checked against the current `stdlib/prelude.cl` re-exports (prelude.cl:27–39). The re-exported trait methods use operator glyphs (`+`, `-`, `*`, `/`, `<`, `>`, `<=`, `>=`, `=`, `!=`) and word names (`Eq`, `Ord`, `Num`, `Display`, `show`, `str`, `Option`, `Some`, `None`, `Result`, `Ok`, `Err`, `pure`, `do`, `bind!`, `->`, `->>`, `List`, `Nil`, `Cons`, `empty?`, `list`, `vec`, `when`, `unless`, `cond`, `case`, `const`, `const-`, `def`, `def-`). **No collision** with any of the 30 primitive names — primitives use the `add-i64`/`str-concat` shape, trait methods use glyphs or short words. The primitive namespace and the operator/type namespace are disjoint by construction.

**LOC impact in `stdlib/prelude.cl`**: 4 new `(export [primitives [...]])` lines (or a single flattened line if preferred). Plus a 6-line comment block documenting the "why primitives too" rationale. Total: ~10 lines added to a 40-line file.

**Second-order impact on other stdlib modules**: None — per `stdlib/CLAUDE.md` §Conventions, every stdlib module already writes `(import [prelude []])` as a null-import to suppress the implicit prelude glob. Stdlib modules use `(import [primitives [*]])` explicitly where they need primitives. They do not inherit the prelude's primitive re-exports; they are unaffected by Option A.

### Option B — Rewrite the 27 examples to use prelude-exposed operator/trait names

**Shape**: Each example replaces `(add-i64 a b)` → `(+ a b)`, `(eq-i64 a b)` → `(= a b)`, `(str-concat a b)` → `(+ a b)` (or via Display), etc. Using Num/Eq/Ord trait methods and the `str` macro already re-exported through prelude.

**Per-example change count**: Rough estimate based on the primitive-occurrence counts in §1.3 and scanning 5 representative files (01-integers, 04-functions, 05-recursion, 09-strings, 14-vecs): 10–40 line-level edits per file, averaging ~20. Across 27 files, ~500–600 edits.

**Blocking question**: does the current prelude actually expose the needed operators as trait-dispatched equivalents?

- `Num.+, -, *, /` — yes (prelude.cl:29), impls for Int and Float via `num/num.cl`.
- `Eq.=, !=` — yes (prelude.cl:27), impls for Int, Float, Bool, String via `compare/eq.cl`.
- `Ord.<, >, <=, >=` — yes (prelude.cl:28), impls for Int, Float, String via `compare/ord.cl`.
- `Display.show` — yes (prelude.cl:30), handles Int/Float/Bool → String (replacing `int-to-string` etc.).
- `str` macro — yes (prelude.cl:31), handles concatenation (replacing `str-concat`).

**But**: some gaps remain.

- `not` — there is no prelude-exposed trait alternative. `not` **is** a Ring-0 inline primitive, not a trait method. Option B cannot rewrite `(not x)` away; the prelude would still need to expose `not`. Either accept that Option B is not pure (a small primitive list still ships through prelude), or rewrite `(not x)` as `(if x false true)` in every example (cosmetically worse).
- `str-len`, `char-at` — no trait alternative currently re-exported; `text/string.cl` provides `length` etc. but these are not in the Ring-2 prelude per `plan-stdlib.md §4`. Option B would need to either expand the prelude with string functions (slippery slope) or leave examples using explicit `(import [text.string [...]])`.
- `vec-len`, `vec-get`, `vec-set`, `vec-push` — already authorised for prelude re-export per `plan-stdlib.md §4` line 297, but not currently re-exported by `stdlib/prelude.cl` line 35 (which only re-exports `vec` macro). This is a prelude-incompleteness matching the plan, not a rewrite target.

**Side benefit**: Examples become more idiomatic — `(+ 1 2)` reads like Lisp, `(add-i64 1 2)` reads like a compiler primitive. This is educationally cleaner **for a user who already knows traits exist**. For a user reading Ring 0 examples *before traits are introduced*, the trait-dispatched form presupposes material (trait instances, Num, Ord) that hasn't been taught yet. The examples sequence intentionally uses named primitives in early files (01-04) before introducing traits in 15-traits.cl. See `examples/01-integers.cl` line 3–4 comment: *"Ring 0 uses monomorphic named primitives for arithmetic: add-i64, sub-i64, mul-i64, div-i64."* The examples are deliberately primitive-oriented for pedagogical staging — Option B fights this design.

### Option C — Hybrid (expose in prelude + rewrite examples over time)

**Shape**: Do Option A now (tactical fix, ~10 LOC). Schedule examples rewrite as a separate pedagogical-review sweep in a future sprint (deprecation path: early Ring 0–1 files retain bare primitive form for teaching purposes; later Ring 2+ files migrate to trait-dispatched form where it's already more natural).

**Deprecation path story**: None needed — primitives and trait methods coexist at call sites today (the test preamble already imports both). Primitives are not being removed from the language; they are not being hidden from the REPL (they live in `primitives`, importable as `(import [primitives [*]])` for power-user work). The prelude simply re-exports the subset that examples and REPL users commonly reach for — no migration deadline, no deprecation warning.

---

## §3 Decision

**Chosen: Option A.**

**One-sentence rationale**: expose the 30 primitive names the examples use through `stdlib/prelude.cl`, extending the already-sanctioned "some primitives belong in prelude" list (plan-stdlib.md §4 line 297) from 8 to 38 names, because the examples are a pedagogical sequence that intentionally teaches named primitives *before* traits and the prelude should match the surface a learner expects.

### Decision criteria cited

**Decisive — "Optional prelude" principle (root CLAUDE.md §Design Principles)**: Minimality floor only. The principle does not prohibit additions; it prohibits required dependencies. Option A adds to the ceiling of convenience without changing the floor of required-ness — a user can still run with `--no-prelude` (or an empty prelude) and import primitives explicitly. **Supports Option A.**

**Decisive — Principle 8 "no interim infrastructure" (design/arch/CLAUDE.md)**: The `tests/fixtures/preamble_primitives.cl` preamble is interim infrastructure. It exists because the stdlib prelude does not match the REPL/`--run` user surface. Option A eliminates the need for that fixture (or makes it vestigial) by converging the test harness and `--run` onto a single prelude surface. Option B preserves the divergence (tests keep the preamble because the preamble is the repro mechanism; examples rewrite just so `--run` matches; `tests/examples.rs` could then drop the preamble for example tests specifically, but other tests keep it). **Option A converges; Option B perpetuates two surfaces. Supports Option A.**

**Decisive — Plan precedent (`plan-stdlib.md §4` line 297)**: The plan already sanctions prelude-level primitive re-export for a hand-picked list. The principle "some primitives belong in the prelude" is already decided; this doc expands the **quantity**, not the category. Option B would require retracting or narrowing that precedent. **Supports Option A.**

**Informative — Pedagogical ordering of examples (01–08 before 15-traits)**: Files 01–08 are Ring 0 teaching material. They use bare primitives intentionally — the comment blocks explicitly name `add-i64` etc. as the Ring 0 surface, and `15-traits.cl` is where operator/trait dispatch is introduced. Rewriting 01–08 to use traits that the reader has not yet learned inverts the teaching sequence. **Supports Option A.**

**Informative — Principle 6 "complexity budget" (design/arch/CLAUDE.md)**: Option A ~10 LOC, 10 minutes of work. Option B 500–600 edits across 27 files + auditing every example's expected Int output for monomorphisation compatibility under trait dispatch + pedagogical rework of example comments. The cost ratio is >50×. **Supports Option A.**

**Informative — Future-stdlib precedent (Condition 4 rationale)**: The decision shape sets what "belongs in the prelude." Option A establishes: *"anything a user in the REPL or a user learning from `examples/` will reach for is a candidate for prelude re-export."* This is the Clojure-prelude stance (large practical prelude tuned for the interactive user) with minimality discipline from plan-stdlib.md §4 (target ~37 names at full maturity → this sprint lifts it to ~70 with 30 primitives; revisit ceiling at the next stdlib-focused sprint). The precedent is auditable by cross-referencing the enumerated 30 names with the "Ring N surface the examples teach" — each addition justifies itself pedagogically.

### What this decision explicitly does NOT decide

- Whether `str-len`, `char-at`, or other string operations beyond the 30 listed should be re-exported. Option A re-exports only what the 27 examples use. Future-sprint decisions on `text/string.cl` prelude re-exports remain open.
- Whether the ~70-name prelude ceiling that Option A establishes is the permanent ceiling. A future stdlib-focused sprint may trim it (removing `eq-bool` if `=` suffices, removing `int-to-string` if `show` suffices, etc.) once all stdlib modules are complete and a full audit is possible. Option A is an additive step that future trimming can revisit.
- Whether `examples/` should eventually adopt trait-dispatched form. Option C's "rewrite over time" story is left on the table for a future `/examples` pedagogical-review sweep — nothing in Option A blocks it, and it is independent of the `--run` path green/red status.

---

## §4 Implementation plan

### 4.1 Scope estimate

**LOC**: ~10 lines added to `stdlib/prelude.cl` (4 `(export [primitives [...]])` forms + 6 comment lines). Zero changes to any other stdlib module. Zero changes to `examples/*.cl`. Zero changes to compiler source.

**Time**: 15 minutes implementation + test run. ~1 hour if cache-invalidation surprises appear (the prelude is cached; Workstream C's build-marker lands in the same sprint and will help, but a stale `.cranelisp-cache/stdlib/prelude.o` may require manual eviction during development).

### 4.2 File-by-file breakdown

**`stdlib/prelude.cl`** — add four `(export [primitives [...]])` forms after the existing Vec export (line 36). Structure:

```clojure
;; ── Primitive re-exports ─────────────────────────────────────────────
;;
;; Ring 0/1 named primitives are re-exported through the prelude so that
;; `cargo run -- --run examples/FOO.cl` matches the REPL user surface.
;; These coexist with the trait-dispatched operators above (e.g. + and
;; add-i64 both work). See design/stdlib/examples-run-path.md for the
;; decision rationale.

(export [primitives [add-i64 sub-i64 mul-i64 div-i64
                     eq-i64 lt-i64 gt-i64 le-i64 ge-i64
                     not eq-bool]])
(export [primitives [add-f64 sub-f64 mul-f64 div-f64
                     eq-f64 lt-f64 gt-f64 le-f64 ge-f64]])
(export [primitives [str-concat str-eq str-len char-at
                     int-to-string float-to-string bool-to-string]])
(export [primitives [vec-len vec-get vec-set vec-push]])
```

**`stdlib/CLAUDE.md`** — one-sentence update to the "Prelude re-exports" list documenting that the 30 primitives are now re-exported.

**`tests/helpers/mod.rs`** — **no change this sprint**. The `preamble_primitives.cl` mechanism remains for integration tests that deliberately exercise the `primitives` namespace directly (e.g., boundary tests, negative tests for spec §8.3 primitive import semantics). `tests/examples.rs` specifically could drop the preamble and validate that examples run against the real prelude — recommended as a §4.3 regression-guard tightening but optional. See §5.

### 4.3 Regression guard

**Test shape for `/qa` to author** (integration test, new file `tests/examples_run_path.rs` OR extension of `tests/examples.rs`):

**CORRECTION (Sprint 60 Wave 2, post-/examples-rescope)**: the snippet below asserts `status.success()`, which is SPEC-INCORRECT. Per `spec/10-io.md` §10, `main`'s `Int` return value IS the process exit code, and `examples/README.md` rule 4 intentionally returns sum-of-pass-results from `main` (always > 0 by design). The authored test in `tests/examples_run.rs` uses a per-example expected-exit-code table matching `tests/examples.rs:22-232` instead. The snippet remains below as historical context only — do NOT copy it.

```rust
// spec: examples/ — Ring 4 acceptance criterion: `--run` works on every example
// file using the production stdlib prelude (no test-fixture preamble).
//
// This test uses the `cargo run --` binary path (not compile_and_run_simple)
// to validate that the user-facing command matches what tests assert.

#[test]
fn every_example_file_runs_under_stdlib_prelude() {
    let examples_dir = env!("CARGO_MANIFEST_DIR").to_owned() + "/examples";
    let files: Vec<_> = std::fs::read_dir(&examples_dir)
        .unwrap()
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("cl"))
        .collect();

    assert!(!files.is_empty(), "examples/ has no .cl files");

    let mut failures = Vec::new();
    for f in &files {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
            .args(["--run", f.to_str().unwrap()])
            .output()
            .expect("run cranelisp --run");
        if !output.status.success() {
            failures.push(format!(
                "{}: exit={:?}, stderr={}",
                f.display(),
                output.status.code(),
                String::from_utf8_lossy(&output.stderr).lines().next().unwrap_or("")
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} examples failed --run:\n{}",
        failures.len(),
        files.len(),
        failures.join("\n")
    );
}
```

This test **cannot use `compile_and_run_simple`** — that helper short-circuits the `--run` path by injecting the primitives preamble. The test must invoke the binary subprocess (Layer 4 per `tests/CLAUDE.md`), otherwise it re-creates the very divergence this workstream eliminates.

**Second regression guard** (recommended; `/qa` may choose to bundle or separate):

```rust
// spec: stdlib/prelude.cl re-exports the primitive surface needed by
// examples/. If a primitive is removed from the prelude, this fails.
#[test]
fn prelude_re_exports_primitive_surface_examples_need() {
    // Concrete names from design/stdlib/examples-run-path.md §1.3
    let required = &[
        "add-i64", "sub-i64", "mul-i64", "div-i64",
        "eq-i64", "lt-i64", "gt-i64", "le-i64", "ge-i64",
        "not", "eq-bool",
        "add-f64", "sub-f64", "mul-f64", "div-f64",
        "eq-f64", "lt-f64", "gt-f64", "le-f64", "ge-f64",
        "str-concat", "str-eq", "str-len", "char-at",
        "int-to-string", "float-to-string", "bool-to-string",
        "vec-len", "vec-get", "vec-set", "vec-push",
    ];
    // For each name, compile `(defn t [] (NAME ...arg-pattern))` in a bare
    // REPL session with only the stdlib prelude loaded. Assert success.
    // (Signature details: use PrimitiveKind to produce a type-correct
    // arg list per primitive; `/qa` picks the shape.)
    // ...
}
```

The second test ensures **individual** primitive names remain re-exported — so if a future edit to `stdlib/prelude.cl` accidentally drops one primitive without breaking any example (because the example happens to not use that primitive at that specific moment), the failure is localised to the dropped primitive rather than appearing as an opaque `--run` failure on the next example change.

### 4.4 Rollout steps (for `/stdlib` when implementing)

1. Read this doc in full. Note §3 decision criteria and §5 philosophy paragraph for any future prelude-scope conversations.
2. Edit `stdlib/prelude.cl` per §4.2. Preserve the comment-block rationale.
3. Update `stdlib/CLAUDE.md` §"Prelude re-exports" list.
4. Smoke-test: `cargo run -- --run examples/01-integers.cl` — expect `69`. `cargo run -- --run examples/14-vecs.cl` — expect `541`.

   **FIXME(/int or /examples)**: Sprint 60 Workstream F implementation discovered
   that the smoke-test command above does NOT find the prelude by itself. Running
   `cargo run -- --run examples/01-integers.cl` sets `project_root=<cwd>/examples`
   per `resolve_target` (spec §0.5.1 rule 2). Prelude discovery (`resolve_prelude`
   → `assemble_lib_dirs`) then looks for `examples/prelude.cl`, `examples/Cranelisp.toml`,
   `$CRANELISP_LIB`, and `examples/stdlib/` — none exist. Result: no prelude loaded,
   primitives inaccessible as bare names. The primitive re-exports are CORRECT — the
   fix was verified end-to-end with `CRANELISP_LIB=$(pwd)/stdlib cargo run -- --run examples/01-integers.cl`
   → exit=69. Either (a) `/examples` ships a one-line `examples/Cranelisp.toml` with
   `lib-dirs = ["../stdlib"]`, or (b) `/int` changes `--run` semantics so the binary
   falls through to the repo-root `stdlib/` when no project-local one is present,
   or (c) the acceptance command in this doc and in `sprints/SPRINT.md` Workstream F
   changes to include `CRANELISP_LIB=$(pwd)/stdlib`. This is out of scope for
   `/stdlib` — filing for the owning skill to pick up.
5. Hand off to `/qa` for regression-guard test authoring per §4.3 (FIXME(/qa) filed at the top of the new prelude section in this doc if not authored immediately).
6. Phase 5b: `/examples` runs `for f in examples/*.cl; do cargo run -q -- --run "$f" || echo "FAIL: $f"; done` and confirms all 27 green.

---

## §5 Stdlib-philosophy implications

This decision **sharpens** the current stdlib philosophy by making the "minimal prelude" principle quantitative-but-bounded rather than quantitative-only. The prelude is not measured by name count; it is measured by *whether every name pulls its weight against the "user surface" the prelude is meant to match*. The 30 primitives pull their weight because the examples sequence — Cranelisp's teaching artefact — uses them. A future primitive addition justified only by "it's a primitive" would fail this test; a future primitive addition that a forthcoming example or `/repl` demo reaches for would pass. The precedent is *the user surface is the authority*, not *the implementation surface*.

This decision also **preserves** the core principle that nothing in the prelude is *required* — the 30 primitives live in `primitives` and can be imported with `(import [primitives [*]])` by any module that bypasses the prelude. Option A's additions are stable-convenience, not required-infrastructure.

The **bounded** part is important: the decision explicitly does not establish a blanket policy of "re-export everything from every stdlib module through prelude." Future stdlib modules (Map, Set, Seq, string operations beyond the 7 listed, `fn/compose`, `fn/combinators`, testing assertions) remain gated behind explicit `(import ...)` unless a case is made — per this doc's precedent — that the user surface the prelude is matching has expanded to include them. The ceiling is not open-ended; it is *set by observed user need*, and the first audit point is the close of the next stdlib-focused sprint (S62+ per Sprint 60 §Out of Scope).

---

## §6 Cross-skill coordination

No FIXME(/examples) is filed — Option A does not require per-example work; `/examples`'s Phase 5b role reduces to running the 27-file sweep and confirming green, which was already the planned validation.

No FIXME(/spec) is filed — the spec's prelude semantics (§8.4) are unchanged. This decision is about stdlib content, not language mechanics.

No FIXME(/int) is filed — the pipeline's prelude-loading mechanism is unchanged; this is a single stdlib file edit.

FIXME(/qa) is implied by §4.3 and picked up via the standard Workstream-F handoff (the integration test for `--run` over every example is the deliverable `/qa` commits this sprint to make the fix permanent).

---

## §7 Open questions deliberately not resolved here

- Should `parse-int` (listed in plan §4 line 297 as a prelude-re-exported primitive) actually be added? Not in the 30-name list because no current example uses it. **Deferred** — it appears in the plan but no example validates it; a later sprint should either use it or strike it from plan §4.
- Should the prelude also expose `print` or `read-line`? No — IO primitives are platform-provided and explicitly imported per `examples/21-hello-io.cl` pattern. Keeping IO out of the prelude preserves the capability/IO boundary. **Decided no.**
- Should the examples sequence eventually be rewritten to trait-dispatched form (Option C's "over time" path)? Open question for a future `/examples` pedagogical-review sprint. **Deferred.**
