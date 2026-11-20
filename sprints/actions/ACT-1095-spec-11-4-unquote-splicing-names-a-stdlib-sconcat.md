---
id: ACT-1095
title: Spec §11.4 says unquote-splicing needs a standard-library sconcat
status: open
priority: advisory
from: dev
to: spec
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/11-stdlib.md §11.4
  - crates/cranelisp-frontend/src/quasiquote.rs::make_sconcat
  - stdlib/core/syntax.cl
  - stdlib/plan-stdlib.md §6.5
---

## Request

Correct the `~@` paragraph in [§11.4](../../spec/11-stdlib.md#114-writing-a-standard-library).
It says unquote-splicing requires `core.syntax/sconcat`, which a standard
library must provide. That obligation does not exist:

- the expander emits `macros/sconcat` (`make_sconcat` in
  `crates/cranelisp-frontend/src/quasiquote.rs`);
- `stdlib/core/syntax.cl` defines no `sconcat`;
- a library author reading the paragraph would add a function nothing calls.

Whether `macros/sconcat` belongs in §11.4 at all, or only in the macro chapter
and appendix A, is `spec`'s call.

## Evidence

`dev`(stdlib), S124 Phase 6a, on a debug build of `39db1bb1`. A program with no standard library (`CRANELISP_LIB` set to an empty
directory, `--run --no-cache`):

```
(import [primitives [Pure add-i64]])
(defmacro sum [& xs] `(add-i64 0 (add-i64 ~@xs)))
(defn main [] (Pure (sum 2 3)))
```

exits 5. `~@` therefore needs nothing from a standard library.

## Completion evidence

§11.4 no longer requires a library-provided `sconcat`. `dev`(stdlib) then
drops `plan-stdlib.md` §6.5.
