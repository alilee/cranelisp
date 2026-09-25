# L-B1 golden-CLIF corpus — EXCLUSIONS

The corpus admits only green programs
([capture contract](MANIFEST.md#capture-contract)). A shape under an open
failing-not-ignored guard is excluded until that guard passes. Record each
exclusion here with its guard and the corpus extension its fix change-set adds.
When the fix lands, add the newly green shape as a new entry — existing golden
entries stay untouched — and remove its row.

| Excluded shape | Guard(s) (failing-not-ignored) | Extension on fix |
|---|---|---|
| _(none)_ | | |

Defects with no CLIF-emission interaction — display, persistence,
introspection and diagnostic defects — are never excluded shapes.
