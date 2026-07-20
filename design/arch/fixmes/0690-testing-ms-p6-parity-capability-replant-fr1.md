---
number: 0690
target: /testing
filed_by: /dev
filed_at: 2026-07-20
sprint_filed: 114
refers_to: tests/ms_p6_mode_self_tests.rs::m3_parity_catches_planted_leak (LEAK_PROG const)
status: open
---

# MS-P6 parity capability cell plants the now-fixed F-R1 teardown leak — re-plant on a synthetic fault

The W4 Track-B backend consume family landed the F-R1 fix (FIXME 0688 verdict a):
`compiler/rc_emission.rs::protect_return_value` no longer over-incs the entry-`main`
IO result, so `(defn main [] (let [s "hi"] (Pure 9)))` now balances
`allocs == deallocs` exactly (the `entry_main_heap_let_teardown_balances_r2` flip).

`ms_p6_mode_self_tests.rs::m3_parity_catches_planted_leak` uses **that exact program**
as its planted fault:

```rust
const LEAK_PROG: &str = "(defn main [] (let [s \"hi\"] (Pure 9)))\n";
```

The cell asserts that `CRANELISP_ALLOC_PARITY` **aborts** on the planted teardown
imbalance. Since F-R1 removed the imbalance, the parity mode no longer aborts
(the program exits 9, balanced) and the capability cell **inverts to RED**. This
is the SAME flip-hazard the plan §3.6 anticipated for the MS-P7 MS-P6 cell:
"the capability cell uses the LIVE defect as its planted fault — it INVERTS to RED
the moment [the defect] is fixed. /testing re-plants it on a synthetic fault (or
retires the cell with rationale)."

**Not a regression** — the parity mode still works; its planted fault is simply
gone. Backend verified in isolation: `m3_parity_no_false_abort_on_clean` (the
clean-program twin) stays GREEN, so the parity detector itself is intact; only
`m3_parity_catches_planted_leak`'s planted `LEAK_PROG` is now balanced.

**Ask:** re-plant `LEAK_PROG` on a synthetic leak the F-R1 (and the general
G2/item-26) fixes do NOT balance — e.g. a shape whose teardown genuinely leaks
and is not entry-`main`'s single-consumer IO result — so the parity capability is
demonstrated against a live imbalance again. (Backend note: the general G2/item-26
protect over-inc is UNTOUCHED by F-R1 — a non-`main` fresh-`Apply` return with a
heap cleanup target still leaks, e.g. `(defn g [] (let [s "hi"] (Pure 9)))` called
from `main`; that residual is a candidate synthetic planted fault.)
