---
number: 0342
target: /typecheck
filed_by: /stdlib
filed_at: 2026-06-13
sprint_filed: 81
refers_to: spec/08-modules.md §8.4 (super import), src/imports.rs, crates/cranelisp-typecheck/src/resolve.rs
status: open
---

# `(import [super [name]])` does not resolve the parent module's symbols — `'name' not found in module '<parent>'`

## Issue (S81 W-I-5 /stdlib finding)

A child submodule that imports a parent symbol via `super` fails to resolve it,
even for a plain `defn` and even when the parent is a top-level file module:

```clojure
;; superp.cl
(import [prelude []])
(defn helper [x] x)
(mod test
  (import [super [helper]])
  (import [primitives [Option Some None eq-i64]])
  (defn test-h [] :(Option String)
    (if (eq-i64 (helper 5) 5) None (Some "no"))))
```

Loading `superp` (e.g. `(import [superp [helper]])`) fails:

```
dependency 'superp.test' failed: type error at …: 'helper' not found in module 'superp'
```

The same failure occurs for a parent `deftype` constructor
(`(import [super [Box]])` → `'Box' not found in module 'superp'`). So the
submodule cannot see the parent's functions OR types.

Spec §8.4 states `super` is supported for one-directional child→parent imports
(only the parent↔child MUTUAL-import cycle is the known-deadlock limitation). A
plain child→parent `super` import is conforming and MUST resolve, but currently
does not — the parent's symbols are not visible to the submodule at the time the
submodule typechecks (an ordering issue: the submodule appears to typecheck
before the parent's definitions are registered/visible to it).

**Pre-existing** (no stdlib module currently ships a working `(mod test)` block;
this is why). It is distinct from the §8.4 mutual-import deadlock — there is no
cycle here.

## Proposed resolution

`/qa` authors a minimal failing repro: a single parent file with one `defn` and
one `deftype`, a `(mod test)` doing `(import [super [fn ctor]])`, imported from a
third file. `// spec:` → spec/08-modules.md §8.4. Decide ownership between
`/typecheck` (resolution) and `/int` (module-load ordering) per
tests/CLAUDE.md §"Isolating Cross-Crate Failures" — the visible error is a
typecheck "not found", but the root cause may be int's module-orchestration
ordering (the submodule's typecheck firing before the parent's symbols land in
the shared tables).

## Operational implication

Blocks `(mod test)` self-tests in stdlib that need parent symbols. The S81 test
runner validated via the REPL demo instead. The design's `discover-tests` path
(observe the parent at RUNTIME, no super import) is the deliberate workaround for
the mutual-import case, but a plain non-cyclic `super` import should still work.
