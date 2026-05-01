---
number: 0015
title: Ring 0-1 `BuiltinFn` coexists with Ring 2 `TraitMethod`
status: operative
---

# 0015 — Ring 0-1 `BuiltinFn` coexists with Ring 2 `TraitMethod`

named primitives (`add-i64`, etc.) retain their `BuiltinFn` resolution path. Operators (`+`, `-`, etc.) gain a new `TraitMethod` path. Both paths coexist per principle 9.
