# stdlib/

Standard library for Cranelisp, written in Cranelisp. Owned by the `/stdlib` skill.

**`stdlib/plan-stdlib.md` is the normative source** for the module tree (§3.2/§3.3),
the curated managed-surface model (§1.5), the prelude contents (§4), the null-import
surface (§15), and per-module delivery status. This file carries only the current
state and the conventions a module author needs at the keyboard — do **not**
re-inventory modules or re-list "what works" here; that duplicates the plan and
decays. When they disagree, the plan wins.

## Current State

The project is in **Phase H (release compiler)**; the ring model that once gated
stdlib build order was retired as a scheduling axis in Sprint 64. Effect and
concurrency support has landed (S94/S96), so IO combinators and parallel library
functions are live rather than blocked.

The stdlib presents a **managed, curated surface** (§1.5): users think in
Clojure-aligned vocabulary (`(+ a b)`, `(= a b)`, `(< a b)`, `(show x)`,
`(str …)`, `(count v)`) — never raw primitive names (`add-i64`, `eq-i64`,
`vec-get`). The de-leak landed at S86: the prelude no longer bare-re-exports raw
primitives; it re-exports only traits/operators, the common types, and the bare
type refs `Int Bool Float String`. Reserved bare collection verbs
(`first`/`rest`/`get`/`count`/`map`/…) stay module-qualified pending Phase-H
trait dispatch (spec `11-stdlib.md` §11.4a); the import path works today.

`prelude.cl` is a **pure re-export shell** — `(export …)` forms only, zero inline
definitions. Every domain module carries `(import [prelude []])` (37 of the 38
non-test modules; the prelude itself is the exception). Notable modules beyond the
plan's Ring-2/3 core:

- `num/bits.cl` — thin, curated layer over the 7 **native** bitwise primitives
  (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`; spec appendix-A
  §A.3). Full **64-bit two's-complement**: `bit-not 0 = -1`, `popcount -1 = 64`.
  This replaced the pre-S91 30-bit arithmetic-simulation module (`pow2`/`width`/
  `bit-at`); those width-capped helpers are gone. Names are module-qualified, not
  bare-promoted.
- `collections/parallel.cl` — `par-map`/`par-reduce`/`par-map-reduce` are
  **ordinary library functions**, not primitives or syntax. They parallelise via
  the inferred lenient-evaluation sparking substrate (`design/backend/lenient-eval.md`,
  `design/arch/effect-concurrency.md` §7): divide-and-conquer over half-open index
  ranges with two independent `let` bindings per node.
- `seq/lazy.cl` — lazy sequences via thunks (`SeqNil`/`SeqCons`; spec
  `12-runtime.md` §12.4.2).

## How stdlib is loaded and exercised

`stdlib/prelude.cl` is auto-discovered as a library prelude by the production
binary. `assemble_lib_dirs` (`src/session_setup.rs`) unions `CRANELISP_LIB`,
`Cranelisp.toml` lib-dirs, and `{project_root}/stdlib/` (searched last); a local
`{project_root}/prelude.cl` overrides. From the repo root the default tier picks up
`stdlib/` automatically.

Self-tests run via the **in-language runner** in a live REPL session (the only mode
where `discover-tests` — a host-promised extern — resolves):

```
(import [<module> [<a-public-name>]])          ; force-load the module
(import [testing.runner [run-one tally tally-line]])
(import [collections.vec [vec-map]])
(import [primitives [discover-tests]])
(tally-line (tally (vec-map run-one (discover-tests ["<module>.test"]))))
```

The pure runner helpers (`run-one`, `tally`, `report`, `passed?`) work in every
mode; only discovery is REPL-only.

## Stdlib separation invariant

Tests (`tests/`) and examples (`examples/`) MUST NOT depend on `stdlib/` — they are
free-standing and define helpers inline from primitives and special forms. Only
`exemplar/` and the production binary (`src/main.rs`) may depend on the stdlib.
Canonical statement: root `CLAUDE.md` §Design Principles ("Stdlib separation"). The
directory is named `stdlib/` (not `lib/`) so accidental coupling is visible. You do
not write code for `tests/` (owned by `/qa`+`/testing`) or `examples/` (owned by
`/examples`); your test code lives inside `stdlib/` as self-tests.

## Conventions

- **Modular, not monolithic.** No file exceeds ~100 lines of public API. Shell
  modules (`compare.cl`, `num.cl`, …) contain only `(mod …)` declarations;
  definitions live in the domain submodules.
- **Prelude is a re-export shell.** `(export …)` only — no `defmacro`, no `defn`.
- **Null-import in every module.** Every stdlib module includes `(import [prelude []])`
  (spec §8.3.6) to suppress the implicit prelude glob (§8.8.1): a project's custom
  prelude may re-export you, and importing from a prelude that depends on you is a
  cycle. Stdlib modules use only primitives and explicit inter-module imports.
- **Self-tests ship as SEPARATE backing files.** Author `<module-dir>/<stem>/test.cl`
  (module `<module>.test`) and leave a **bare `(mod test)`** in the parent — do NOT
  author inline `(mod test …)` bodies. The compiler extracts an inline body to that
  backing path on first compile (spec §8.2.5), but the extraction does not write the
  file when the lib dir is the in-place workspace `stdlib/`, so an inline body is
  silently stripped (a full `cargo nextest run` corrupted the tree this way, S87).
  Authoring the backing file directly is extraction-stable. 17 modules currently
  carry backing self-tests. Test functions use the `test-*` naming convention for
  `discover-tests`.
- **Clojure alignment.** Follow `clojure.core` naming and design where possible.
- **Trait method params** use `self` syntax (spec §7.1). Primitive names match the
  builtins table exactly (`add-i64`, `str-concat`, …; spec appendix-A).
- Modules outside the prelude graph (e.g. `derive.cl`) use primitives directly, not
  trait operators.

## Gotchas

- **Stale cache masks stdlib edits.** REPL/`--run` runs persist a `.cranelisp-cache`
  in the CWD; a stale root cache surfaces confusing errors (e.g. "no impl of trait
  Ord for Bool" when the impl is present). Clear `./.cranelisp-cache` or pass
  `--no-cache` when testing stdlib changes from the repo root.
- **`Ord String`** needs a code-point comparison primitive; the string surface can
  test char equality but not order differing chars (usability finding, open).

## Defect handoff

When exercising the language to build stdlib surfaces a **compiler/runtime defect**
(wrong values, spec-permitted signatures rejected, crashes, REPL/`--run`
divergence), the wave is not closed until `/testing` has a narrow, failing,
un-ignored repro annotated with `// spec:` naming the violated section. Defects in
the stdlib *code itself* are `/stdlib`'s own to fix; this handoff is for defects in
the **language**, surfaced by stdlib composing primitives at scale. See root
`CLAUDE.md` §"Usability Findings and Defects".
