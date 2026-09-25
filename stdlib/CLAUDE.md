# stdlib/

The reference standard library, written in Cranelisp. `dev`, narrow-deployed
to `stdlib/`, owns the modules, their self-tests and this directory's
documents (root [roles](../CLAUDE.md#roles)).

- [Standard library design](plan-stdlib.md) holds the curated surface and
  prelude, the module map, the self-test model, the unbuilt surface, the
  requested-function backlog and the open stdlib decisions. Do not restate it
  here.
- Module source is the authority for exact names; `prelude.cl`'s `(export …)`
  forms are the prelude-bound set.
- [Spec §11](../spec/11-stdlib.md) states the language's guarantees to library
  authors.

## Loading and running self-tests

- The binary searches `CRANELISP_LIB`, then `Cranelisp.toml` lib-dirs, then
  `{project_root}/stdlib/` (`assemble_lib_dirs` in `src/session_setup.rs`). A
  project-root `prelude.cl` overrides the stdlib prelude.
- Discovery (`discover-tests`) resolves only in a live REPL session. The pure
  runner helpers (`run-one`, `tally`, `report`, `passed?`) work in every mode.
- Run one module's self-tests from a REPL:

```
(import [<module> [<a-public-name>]])          ; force-load the module
(import [testing.runner [run-one tally tally-line]])
(import [collections.vec [vec-map]])
(import [primitives [discover-tests]])
(tally-line (tally (vec-map run-one (discover-tests ["<module>.test"]))))
```

- The force-load line must name a real public symbol. A null import
  (`(import [<module> []])`) compiles the module without enrolling its private
  test child, so the recipe reports zero tests: a false green.

## Conventions

- **Separation.** `tests/` and `examples/` must not depend on `stdlib/` (root
  [design principles](../CLAUDE.md#design-principles)). Stdlib evidence lives
  here as self-tests.
- **Shells and prelude.** Shell modules only declare submodules.
  `prelude.cl` only re-exports; it has no `defn` or `defmacro`.
- **Null import in every module except the prelude.** Each module carries
  `(import [prelude []])` (spec §8.3.6), because a project prelude may
  re-export it and importing that prelude would form a cycle. Modules use
  primitives and explicit inter-module imports only.
- **Self-tests are backing files behind a private declaration.**
  - Author `<module-dir>/<stem>/test.cl` (module `<module>.test`), and put
    `(mod- test)` in the parent.
  - A public `(mod test)` makes the test functions importable and searchable,
    so do not use it.
  - Do not author an inline `(mod test …)` body. S87 observed first-compile
    extraction (spec §8.2.5) strip inline bodies without writing the backing
    file when the lib dir is the in-place `stdlib/`, which corrupted the tree.
- **Ship tests with every definition-bearing module.** The S115 sweep found
  every stdlib defect in untested modules.
- **Enumerate withheld cases.** When a compiler defect caps coverage, ship the
  cases that run and list the withheld ones in the test header, as
  `derive/test.cl` does.
- **Do not work around a language gap.**
  - A stdlib workaround for a compiler or language defect hides the defect
    from the conformance gate and bakes the workaround into model code.
  - Route the gap as a defect or action instead.
  - Add a stdlib function only when it composes from existing primitives,
    ships with self-tests, and stays clear of the reserved names in the
    design's §1.5.
- **Clojure alignment and naming** follow the design's §1.3. Trait method
  parameters use `self` (spec §7.1). Primitive names match appendix A exactly.
- **Accessors.** Sum payloads do not mint accessors. Only a deftype-level field
  list on a same-named product mints `Type.field` and its bare alias.
  Destructure other payloads with `match` and write field verbs by hand, as
  `collections.list` and `collections.pair` do.

## Gotchas

- **A stale cache masks stdlib edits.** REPL and `--run` persist
  `.cranelisp-cache` in the working directory. Clear it or pass `--no-cache`
  when testing stdlib changes; a stale cache produces misleading errors.
- **A cache-restored parent does not enrol its private test child**
  ([FIXME 0868](../design/arch/fixmes/0868-cache-restored-parent-does-not-enrol-private-child.md)).
  A second REPL process then finds no tests, so run self-tests with a cold
  cache.
- Probe from your own scratch directory with `CRANELISP_LIB` set, never from
  the repo root ([probe hygiene](../sprints/METHOD.md#22-phase-notes)).

## Defect handoff

A defect in stdlib code is `dev`'s to fix here. A language or runtime defect
found while composing the library needs a minimal repro. The wave does not
close until `test` has committed a narrow, failing, un-ignored reproduction with
a `// spec:` annotation (root [usability findings and defects](../CLAUDE.md#usability-findings-and-defects)).
