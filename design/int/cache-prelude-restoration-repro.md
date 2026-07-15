> **HISTORICAL — superseded / completed working doc (triaged S110, FIXME 0607).** A
> point-in-time record retained for the audit trail only; NOT current design intent. The
> durable design is `int.md` (master) plus the subsystem docs indexed in
> `design/int/CLAUDE.md` §"Document index". Where this doc disagrees with the current source
> or the master, the source and master win.

# Cache-hit prelude restoration: diagnostic repro (Sprint 59 Wave 1)

**Status**: diagnosis-only (no fix).
**Owner**: `/int` (session wiring; worker prelude injection).
**Carried test**: `tests/sprint23.rs::cache_repl_loads_on_startup`.
**Repro test**: `tests/sprint59_cache_repro.rs::s59_cache_hit_plain_prelude_fn_not_restored`.
**Prepared**: 2026-04-20, after `/backend`'s Wave 1 GOT_LOAD local-symbol
fix (previously surfaced as `.Ldata0` relocation failure — now resolved).

## 1. Failure signature

Running the REPL twice in the same project directory with a local prelude:

```
Session 1 (populate cache):
  cranelisp REPL — type /help for help
  0+0ms; user> :primitives/Int 42
  0+0ms; user>

Session 2 (cache hit):
  cranelisp REPL — type /help for help
  0+0ms; user> Error: type error at 1..2: undefined variable: +
  0+0ms; user>
```

(The carried test uses `(+ 40 2)` against `tests/fixtures/prelude.cl`.
The minimal repro below shows the same shape with a single non-operator
plain function.)

## 2. Minimal repro

File: `tests/sprint59_cache_repro.rs` (already committed as failing,
NOT `#[ignore]`'d — per `feedback_failing_not_ignored.md`).

Two tests, both driving the shipped `cranelisp` binary as a subprocess:

### A. `s59_cache_hit_plain_prelude_fn_not_restored` — FAILS

The smallest prelude that reproduces the bug is **one plain top-level
function, no operators, no traits, no impls, no ADTs**:

```rust
std::fs::write(lib.join("prelude.cl"), "(defn f [] 42)\n").unwrap();
// Session 1: (f)  -> 42   cache manifest created
// Session 2: (f)  -> Error: undefined variable: f
```

Session 2 stderr is empty; the `undefined variable` surfaces as a
*type error* at column 1..2, which means the name never reaches
codegen — the typechecker has no binding for `f` in the `user`
module.

### B. `s59_cache_hit_empty_prelude_basic_eval_works` — PASSES

Prelude is empty (`;; empty\n`), input is a literal `42`. Both sessions
print `42`. This confirms:

- the REPL startup pathway itself is healthy on cache hit;
- the bug specifically concerns **binding rebinding** from cached
  prelude into the new session's per-module typecheck state;
- it is NOT triggered by the cache-hit machinery alone.

### Scope of the reduction

| Variable | Reduction A | Reduction B | Result |
|---|---|---|---|
| Prelude has one plain `defn` | yes | no | A fails |
| Prelude exports via `(import [primitives [*]])` | no | no | A fails |
| Operators / traits / `impl`s needed | no | no | A fails |
| ADTs (`Option`, `Result`) defined | no | no | A fails |

Conclusion: **any prelude binding suffices** to trigger the bug. The
Sprint 58 triage framing ("`+` missing") was symptom-accurate but
scope-narrow: all prelude-exported names are affected equally.

### Library-level repro attempt

A pure Rust-API repro (using `ReplSession::new_with_prelude` from
`tests/helpers/mod.rs` twice against a scratch cache dir) was
considered. It was **not attempted** because the `ReplSession` test
helper sets `no_cache: true`, so the cache pathway is never exercised
through that API. A library-level repro would require a new helper
constructor that enables caching; adding that helper is out of scope
for diagnosis-only work and would itself require `/int` to decide
whether it belongs in the public surface. The subprocess repro is
sufficient and matches the production startup flow exactly. Noted as
a follow-up convenience for the fix wave (estimated <15 min).

## 3. Session 2 symbol-table state for `f` / `+`

**Classification: present-but-not-reached.**

Walking `src/worker.rs::inject_prelude_if_needed` (lines 2266–2339)
against the cache-hit path:

```rust
if !ctx.symbol_tables.contains_key(&prelude_path) {
    …
    if let Some(prelude_file) = prelude_file {
        if try_cache_hit_load(ctx, &prelude_path, &prelude_file) {
            // Prelude loaded from cache — inject implicit import and continue.
            return Ok(None);        // <-- BUG: no register_imports call
        }
        …
    }
} else {
    // Prelude already loaded — register the import.
    let prelude_spec = ImportSpec { … ImportNames::Glob, … };
    cranelisp_typecheck::TypeCheckEnv::new(ctx.symbol_tables, ctx.next_type_id)
        .register_imports(&mut ctx.check_state, &[prelude_spec])?;   // <-- correct path
}
```

After `try_cache_hit_load` returns `true`:

- `ctx.symbol_tables` DOES have a `prelude` entry (populated by
  `restore_cached_module` at `worker.rs:1484-1487`). Symbol `f`
  (or `+`) is **present** there, with `Code: None` — JIT codegen will
  populate a fresh `Code::Linker` entry on demand.
- `ctx.check_state` for the `user` module has **no glob import of
  `prelude`** recorded. When the REPL evaluates `(f)`, typecheck
  name resolution looks only at `user`'s directly-visible bindings
  plus its registered imports. The `prelude` entry is never consulted.

The comment on line 2290 (`"Prelude loaded from cache — inject
implicit import and continue."`) is aspirational — the implicit
import is NOT injected in this branch. The "else" branch (2327-2336)
shows the correct shape and can be copy-pasted.

## 4. Affected scope

Not just `+`, and not just operators. **Every prelude-exported symbol**
is missed:

- plain `defn` names (confirmed — minimal repro);
- operator names (`+`, `-`, …) — they are `defn`s in the test prelude
  (`tests/fixtures/prelude.cl:27-37`), so same code path;
- trait method names, ADT constructors (`Some`, `None`, `Ok`, `Err`)
  — same code path, all arrive as `Def`/`Constructor` entries in the
  cached symbol table.

A single fix at the `inject_prelude_if_needed` cache-hit branch
restores all of them.

## 5. Classification — which crate owns the fix

**(b) `/int` session wiring** — specifically `src/worker.rs`
at the `inject_prelude_if_needed` cache-hit return site.

Not `/backend` cache read: `try_cache_hit_load` already correctly
installs the prelude's symbol table, GOT, and platform bindings.
The `/backend` Wave 1 fix resolved the GOT_LOAD `.Ldata0` relocation
that previously masked this bug.

Not `/int` session persistence (dual-path collapse workstream A):
Workstream A landed; its fix set `persist_import_survives_restart` and
`v4_cache_hit_dependency` to green as expected. This is a separate,
narrower defect in the prelude-specific injection helper that
Workstream A did not touch. (Workstream A targets
user-authored `(import …)` forms; this targets the implicit glob
`(import [prelude [*]])`.)

## 6. Suggested unit test location for the fix wave

Add to `src/worker.rs` inside its `#[cfg(test)] mod tests`:

```rust
#[test]
fn inject_prelude_if_needed_registers_glob_import_on_cache_hit() {
    // Given: shared state where `prelude` is already in `symbol_tables`
    // (simulating a just-completed `try_cache_hit_load`).
    // When: inject_prelude_if_needed runs on a fresh `user` module.
    // Then: `ctx.check_state` for `user` contains an `ImportSpec` for
    //       `prelude` with `ImportNames::Glob`.
}
```

The existing "else" branch (line 2327-2336) is the oracle for the
assertion. A complementary test for the fresh-load case
(`try_cache_hit_load` returns `false`, scheduler blocks, glob is
registered post-block) already exists implicitly via every integration
test — the unit test need only cover the cache-hit branch.

## 7. Estimated fix effort

**S (small, <2 hours).** The fix is one copy of the four-line
`register_imports` block from the "else" arm into the cache-hit arm
of `inject_prelude_if_needed`. No cross-crate impact, no data-model
change, no spec or design-doc restructure.

Breakdown:

- Code change: ~5 min (copy-paste from line 2329-2335).
- Unit test (per §6): ~45 min.
- Verify `sprint23::cache_repl_loads_on_startup` +
  `tests/sprint59_cache_repro.rs` flip green; run full `sprint23`
  suite + `cache` suite for regression: ~15 min.
- Total: ~1 hour active work, ~2 hours with review.

## 8. Repro instructions

```bash
# Baseline (pre-existing carry — should FAIL):
cargo nextest run --test sprint23 cache_repl_loads_on_startup

# Minimal reduction (new, committed un-ignored — should FAIL):
cargo nextest run --test sprint59_cache_repro s59_cache_hit_plain_prelude_fn_not_restored

# Control (minimal — should PASS):
cargo nextest run --test sprint59_cache_repro s59_cache_hit_empty_prelude_basic_eval_works
```

After the fix in §5, all three are expected to go green.
