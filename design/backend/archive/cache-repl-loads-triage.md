# Triage: `sprint23::cache_repl_loads_on_startup`

**Status**: triage-only (Sprint 59 Wave 1). No fix authored.
**Owner**: `/backend` (cache linker).
**Prepared**: 2026-04-20.

## Failure signature

Second REPL session on a populated cache fails to load `prelude.o`:

```
error: module error at 0..0: module 'prelude' failed: codegen error at 0..0:
GOT_LOAD relocation: unresolved symbol '.Ldata0' (cannot allocate slot for unknown address)
```

Source: `crates/cranelisp-backend/src/cache/linker.rs:146-152` — error raised
inside `Linker::ensure_got_slot` when the relocation's target symbol cannot be
found in either `self.defined_symbols` or `self.symbols`.

The `nextest` assertion that fires first is at `tests/sprint23.rs:1184-1187`:
the second run produces empty stdout (no `:primitives/Int 42`) because REPL
startup aborted on prelude load. The session-1 run succeeds and populates the
cache (`prelude.meta.json`, `prelude.o`, `user.meta.json`, `user.o`,
`manifest.json`) exactly as expected.

## Repro

```bash
cargo nextest run --test sprint23 cache_repl_loads_on_startup
```

Run once only (the test exercises both session 1 = populate, session 2 = load).
Confirmed via hand-repro in an empty scratch directory: first `cranelisp` run
with `CRANELISP_LIB=tests/fixtures` prints `:primitives/Int 42`; the second run
in the same directory prints the GOT_LOAD error above and never reaches the
REPL prompt.

## Root cause

**Classification: D (Linker GOT-resolution lookup-surface gap).** The Linker
has all the data required to resolve the relocation, but `ensure_got_slot`
searches the wrong subset of symbol tables.

### What `.Ldata0` is

`.Ldata0` and `.Ldata1` are Cranelift-internal local data labels — not source
names. `cranelift-object` emits them for string-literal constants (runtime
panic message bodies) into `__const` on Mach-O. Verified via `nm` and `otool`
on the persisted `prelude.o`:

```
00000000000003b0 s _.Ldata0      # __const, "arity mismatch"-class message
00000000000003c0 s _.Ldata1      # __const, sibling message
```

The lowercase `s` symbol type means "local data symbol, private to this
object" — exactly the Mach-O analogue of an assembler `.L`-prefixed label. In
the text section there are GOT_LOAD relocation pairs against them:

```
000000f4  GOTLDPOFF  _.Ldata0     # ARM64_RELOC_GOT_LOAD_PAGEOFF12
000000f0  GOTLDP     _.Ldata0     # ARM64_RELOC_GOT_LOAD_PAGE21
000000d0  GOTLDPOFF  _.Ldata1
000000cc  GOTLDP     _.Ldata1
```

So Cranelift compiled the string-constant reference as an ADRP+LDR sequence
via the system GOT — the same mechanism used for cross-module imports.

### Why session 1 works and session 2 fails

Session 1 never goes through the cache Linker: it compiles via Cranelift's
JIT, which resolves string-literal `global_value` references in-memory via
the JIT's own symbol table. No `.o` relocation fixup is involved.

Session 2 hits the cache — it reads `prelude.o` from disk and calls
`Linker::load_object` to install it. The `.o` *does* contain the `.Ldata0`
body in `__const` and a symbol definition pointing at it. `load_data_sections`
at `linker.rs:402-465` handles this correctly: when a data-section symbol's
name starts with `.L` it is inserted into the *per-object* `local_symbols`
map (`linker.rs:449-454`), not into `self.defined_symbols`.

The text-section relocation loop at `linker.rs:275-367` then processes each
reloc. For the `.Ldata0` GOT_LOAD pair:

1. `target_name` = `".Ldata0"` (linker.rs:288).
2. `raw_target_addr` is looked up across `local_symbols` → `self.defined_symbols`
   → `self.symbols` (linker.rs:298-306). **This succeeds** — `local_symbols`
   contains `.Ldata0`.
3. The relocation type is `ARM64_RELOC_GOT_LOAD_PAGE21` /
   `ARM64_RELOC_GOT_LOAD_PAGEOFF12`, so the code at `linker.rs:320-327`
   delegates to `ensure_got_slot(&target_name)` to allocate the in-process
   GOT slot.
4. `ensure_got_slot` (linker.rs:137-152) only consults `self.defined_symbols`
   and `self.symbols`. **It never sees `local_symbols`.** So despite the
   outer loop having already resolved `.Ldata0` successfully, slot
   allocation fails with "unresolved symbol".

The failure is a contract mismatch between the outer relocation loop (which
correctly treats `local_symbols` as first-priority) and `ensure_got_slot`
(which is ignorant of it). The fix adjusts the Linker's internal API to
propagate the already-resolved address — it does not require any new codegen
or object-emission work.

### Why this was not caught by the Sprint 58 Wave 2 Decision 23 test

The regression-guard test at `linker.rs:684-802`
(`linker_resolves_arm64_got_load_relocations`) exercises the GOT_LOAD path
against an `Linkage::Import` data symbol (`__cranelisp_got_imported`) — a
global external symbol, so it lives in `self.symbols` and `ensure_got_slot`
succeeds. The test does not synthesise a case where GOT_LOAD targets a local
`.L`-prefixed data symbol. Cranelift only emits GOT_LOAD for `.L*` locals
when an ADRP+LDR pair is required for a constant-pool entry, which happens
for string-literal arguments to intrinsic calls — the exact pattern that
appears in `prelude.cl` trait-method dispatchers that raise runtime panics
(e.g. arity-mismatch or type-error messages).

## Effort estimate

**S (small, <1 day).** The fix is confined to `ensure_got_slot` and its call
site. No cross-crate impact, no data-layout change, no spec or design-doc
restructure.

Rationale:

- One call site (`linker.rs:325`), one bug site (`linker.rs:137-152`).
- The data needed for the fix is already in-hand at the call site
  (`raw_target_addr`, the successful outer lookup).
- Three plausible fix shapes (below) are all narrow; choice is stylistic.
- Regression guard pattern exists — the Sprint 58 Decision 23 test provides
  a copy-paste template for a new test that uses a `.L`-prefixed data
  symbol instead of an Import symbol.

Time budget:

- Fix: ~30 min.
- Unit test (in `linker.rs` tests module, synthesise `.o` with a
  `.L`-local data symbol referenced via GOT_LOAD): ~1 hour.
- Verify `cache_repl_loads_on_startup` flips green + full sprint23 suite
  clean: ~10 min.
- Total: ~2 hours of active work.

## Fix surface

All changes confined to `crates/cranelisp-backend/src/cache/linker.rs`.

- `Linker::ensure_got_slot` — accept the pre-resolved `symbol_addr: usize`
  from the caller instead of re-looking-up by name, **or** accept a
  `local_symbols: &HashMap<String, usize>` parameter and fall through to it.
- `Linker::load_object` at `linker.rs:320-327` — pass the pre-resolved
  `raw_target_addr` (or `local_symbols`) through.
- New test `linker_resolves_got_load_for_local_data_symbol` alongside the
  existing `linker_resolves_arm64_got_load_relocations` — synthesises an `.o`
  with a `__const` `.L`-local symbol referenced by a GOT_LOAD relocation,
  asserts the Linker allocates a slot containing the local symbol's address.

Preferred shape (stylistic): pass `symbol_addr: usize` — keeps
`ensure_got_slot` a pure slot allocator with no symbol-table coupling, which
matches its doc-comment contract ("allocate a slot and initialise it with the
given address"). This inverts the current relationship (caller resolves,
Linker caches) but reads cleaner.

## Cross-cutting implications

**None outside `/backend`.** The fix does not touch:

- `/int`'s Workstream A persistence collapse (already landed — Workstream A
  delivered as scoped, per /int's handoff; the other two A-target tests
  `persist_import_survives_restart` and `v4_cache_hit_dependency` flipped green
  as predicted, and the heisenbug parallel-stress guard remains rock-solid).
- `compile_to_module` or `cranelift-object` emission — the `.o` is already
  correct; the bug is in consumption.
- Spec, design docs, or cache schema. `design/backend/module-caching.md` §9
  covers the Linker but the fix is an implementation-detail patch, not a
  design change. At most a one-line note that `ensure_got_slot` now accepts
  locally-scoped symbols.
- GOT architecture under Decision 23 — the byte-identical CLIF/machine-code
  invariant holds; only the in-process slot-allocation surface widens.

**Other failures this fix resolves**: likely **only this one test.** The
other carried tests in the sprint scope (`persist_defn_survives_restart`,
`defmacro_syntax_survives_restart`, etc.) are filed against different
subsystems (session persistence, macro re-registration) and do not rely on
GOT_LOAD resolution of local data symbols. /int's Workstream A already
restored the two that do. No multi-test cascade anticipated.

**Regression risk**: low. `ensure_got_slot` is only called from one site,
and the `.Ldata*` local-symbol resolution path was already working correctly
for the non-GOT_LOAD relocation types (BRANCH26, PAGE21/PAGEOFF12) — the
existing data-section tests in `tests/cache.rs` exercise that surface.

## /sprint recommendation

**Fold into Sprint 59 as a small add-on to Workstream C (or a satellite Wave
1 task).** Rationale: this is an S-sized, bounded, /backend-local fix with
a clear reproducer, a copy-paste test template, and no cross-skill
dependencies. Folding it in achieves the S59 "0 carried failing tests"
milestone without re-scoping any existing workstream. Deferring to S60 would
leave a known-localised Linker bug on the carry list purely for scheduling
convenience, which contradicts the milestone.

One-line: S effort, /backend-local, clear repro and fix shape — fold into
S59 to hit the zero-carry milestone.
