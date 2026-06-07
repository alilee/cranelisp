---
number: 0235
target: /qa
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §12 (Next skills), tests/plan/sprint71-platform.md §4, FIXME 0229, FIXME 0233
status: open
---

## Progress (S76 W3, /qa) — round-trip STILL BLOCKED; construction primitive necessary-but-insufficient

/qa attempted the unblocked round-trip half this fire and found it is **not yet
unblocked** — and the residual blocker is broader than the schema-validation seam
(0282) named in the work order.

**What landed (necessary, not sufficient):** `alloc_with_tag` (the host-side ADT
*construction* primitive) is wired + unit-verified (0229 step 1). This lets the
host *allocate* a tagged heap-ADT, but it does NOT make a platform-declared ADT
*referenceable by name* from cranelisp source.

**The hard blocker /qa confirmed by direct probe (NOT 0282):** a platform
function whose `type_sig` names an ADT (e.g. `rectangle-area : (Fn [Rectangle]
Int)`) **fails to typecheck at load** with `unknown type 'Rectangle' (from module
'')`. Reproduced end-to-end with a throwaway `test-adt` cdylib (built against the
workspace `cranelisp-platform`, `schema:` + `schema_types: [Rectangle]`,
`rectangle_area` reading `w`/`h`), loaded via `CRANELISP_PLATFORM_PATH` + `--run`:

```
(platform test-adt)
(import [platform.test-adt [rectangle-area]])
(deftype Rectangle [:Int w :Int h])
(defn main [] (rectangle-area (Rectangle 3 4)))
```

→ `type error in platform function 'rectangle-area' signature '(Fn [Rectangle]
Int)': unknown type 'Rectangle'`.

**Root cause (source-confirmed):** `src/platform.rs::register_platform_in_tc`
registers only the function descriptors (+ injects `(import [primitives [*]])`)
into the synthetic `platform.<name>` module. It does **not** consume the DLL's
`GetSchema`/`DLL_SCHEMA` to register the schema-declared ADT **type defs** — there
is no `register_type_def` for `Rectangle` anywhere in the platform-load path. The
rustdoc on `parse_and_check_platform_type_sig` (`src/platform.rs:355–357`) names
this explicitly as a future seam: schema ADT names resolve *"once the platform
module carries those type defs (host-wiring round-trip; see ... §4 seam
0231/0233)."* That seam is open.

**Disposition:** ALL FOUR 0235 deliverables remain blocked, not just item 4:
- Items 1–3 (test-adt DLL + `tests/spec_platforms_adt.rs` round-trip + cache
  restore) are blocked on the **schema-type-registration seam** — the
  platform-as-module path must register schema-declared ADT type defs so platform
  sigs (and importers) can name them. This is the open half of FIXME 0231/0233
  step 2 (`/int` + `/dev platform`); it is a prerequisite for any CLAdt-typed
  platform function to typecheck. **NOT 0282.**
- Item 4 (schema-typo mismatch → `validate_schema` rejection at load) is blocked
  on the **S-PLAT-1 schema-text-exposure seam** (FIXME 0282, `/arch` ruling
  pending — Option A manifest field vs Option B macro-invokes-callback).

/qa authored NO e2e test this fire: a `tests/spec_platforms_adt.rs` round-trip
would fail at platform-sig typecheck (a different, upstream failure than the
round-trip the test is meant to exercise), and authoring a `platforms/test-adt/`
cdylib is `/platform`'s domain (this FIXME's step-1 DLL author is `/platform`, not
`/qa` — only the `tests/`-side e2e file is `/qa`'s). When the schema-type-
registration seam lands, `/qa` files the failing-first `tests/spec_platforms_adt.rs`
plan and lands items 1–3; item 4 follows once 0282 resolves.

**Recommended next:** file/track the schema-type-registration seam as the
prerequisite for 0235 (it belongs with 0231/0233's open half); keep 0235 open.

# Round-trip integration tests once host-side wiring lands

## Issue

Sprint 71's Wave 2 tests are intra-crate (`crates/cranelisp-platform/tests/*.rs`):
they exercise the marker-type pattern, schema parser, and worked
extern functions against synthetic in-test heap fixtures.

True end-to-end coverage — a real DLL exporting CLAdt-typed functions,
loaded by the host, called from cranelisp source code, with values
crossing the FFI boundary — is deferred until:
- `HostCallbacks::alloc_with_tag` is wired (FIXME 0229).
- Platform-as-module is in place (FIXME 0233) so the cranelisp source
  can reference the platform-declared ADTs by name.

Tests/plan/sprint71-platform.md §4 explicitly defers these to the
host-wiring sprint and tracks them via this FIXME.

## Proposed resolution

In the host-wiring sprint (or the sprint immediately after):

1. **A new test-platform DLL** — `platforms/test-adt/`:
   - `declare_platform!` with a non-trivial schema (Rectangle +
     OptionInt + ListInt; deliberately exercise all three shape
     families).
   - Three extern functions that consume CLAdt parameters and return
     CLInt: `rectangle-area`, `option-or-default`, `list-sum`.

2. **A new test file** — `tests/spec_platforms_adt.rs`:
   - Loads the test-adt platform DLL.
   - Executes cranelisp source that constructs the corresponding
     ADTs via cranelisp-side `deftype` + constructor calls, then
     passes them to the platform fns.
   - Asserts the round-trip values match the expected outputs
     (rectangle of {w=3, h=4} → 12, etc.).

3. **Cache-restore round-trip** — re-load the same project from cache
   and verify ADTs cross correctly post-cache-hit (validates the
   `.meta.json` schema_literal field of FIXME 0232).

4. **Mismatch coverage** — a test that intentionally ships a
   schema-typo'd DLL and verifies the host's `validate_schema`
   callback rejects it at load with a clear error.

## Operational implication / Context

These tests are workspace-integration (under `tests/`) per the
two-tier discipline in `tests/CLAUDE.md`. The intra-crate tests
landed Sprint 71 Wave 2 are the unit/crate-integration tier; this
FIXME closes the e2e tier for the same surface.

Coordinating with the host-wiring sprint: as `/int` implements
FIXMEs 0229–0233, `/qa` files this FIXME's failing-first test plan;
Wave 2 of that sprint lands these round-trip tests as the acceptance
criterion.
