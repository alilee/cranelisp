# Bare-primitive value path: Slice 1 of Sprint 61

**Owner**: `/int`
**Status**: IMPLEMENTED (Sprint 61 Wave 2, 2026-04-21)
**Reviewers**: `/arch`

## Post-implementation note (Sprint 61 Wave 2, 2026-04-21)

**Diagnosis**: Candidate 2 held, with a mechanical twist not isolated in
the pre-implementation design text. The bare-value path falls through
`check_bare_symbol_introspection`'s outer match at `_ => None` for
`Import`/`Reexport` variants — but only because the resolver itself
(`resolve_entry_for_display`) did a **single hop** rather than walking
the full chain. The three-module pattern the user observes is
`user → prelude (Import) → primitives (Reexport) → primitives Def`.
One hop from `user/add-i64` terminates on the `Reexport` entry sitting
in `prelude`'s symbol table; the match then drops through `_ => None`
and the bare-value path falls into `process_single_form`, where
codegen emits `undefined variable: add-i64`.

The typechecker's resolver (`TypeCheckEnv::resolve_to_terminal_entry_owned`,
`crates/cranelisp-typecheck/src/checker.rs:537`) has always been
recursive with an `IMPORT_CHAIN_DEPTH_LIMIT` guard, which is why the
call path `(add-i64 2 3)` resolves correctly — it uses that walker.
The display resolver in `session_v4.rs` was never aligned to that
discipline, so re-exported primitives that pass through two or more
hops land as intermediate `Reexport` entries on the introspection /
bare-value paths but not on the call path. This is the "dual-path"
anti-pattern pattern §6 calls out.

**Fix**: `resolve_entry_for_display` is now a bounded-depth loop
(`MAX_DEPTH = 32`, matching the intent of the typechecker's
`IMPORT_CHAIN_DEPTH_LIMIT`) that walks `Import`/`Reexport` chains to a
terminal non-alias entry. On a broken link it returns the last
resolved pair so display remains best-effort. The bare-value path in
`check_bare_symbol_introspection` additionally threads the resolved
module into the returned `FQSymbol.module` (per spec §8.9 re-export
provenance — introspection MUST display the original defining module).

**Spec implication**: none. The spec correctly treats re-exports as
first-class public names; the defect was a one-hop resolver in the
display layer, not a spec gap. No `FIXME(/spec)` filed.

**Out of scope** (deferred, not regressed by the fix):
- `/sig add-i64` still prints `add-i64 ; imported from prelude/add-i64`
  via `format_entry_sig`'s `ModuleEntry::Import` arm — that handler
  does not consult `resolve_entry_for_display`. Fixing `/sig` to call
  the recursive resolver is a follow-on alignment in the same file;
  not required for Slice 1 acceptance (which was the bare-value path
  specifically) but filed as a candidate for Sprint 62 polish if /repl
  raises it. The call path `(add-i64 2 3)` and the bare-value path
  both now produce the spec-conforming output.

## 1. Problem

Typing `add-i64` at a REPL prompt errors `undefined variable`, but
`/sig add-i64` returns the expected signature and `(add-i64 2 3)`
evaluates to `5`. Re-exported `primitives` names are visible on the
introspection path and the call path but NOT on the bare-value path.

This is a fresh instance of the dual-path anti-pattern established in
Sprint 59 (see `design/int/dual-path-persistence-collapse.md`) — three
code paths for what should be one resolution.

## 2. The three paths

Each path is a separate code route inside `CompilerSession`:

1. **Bare-value path** (bare symbol typed at the prompt, expecting a
   REPL echo of the value or an introspection card).
   Entry: `eval_one_form` → `check_bare_symbol_introspection`
   (`src/session_v4.rs:2179`). Falls through to `process_single_form`
   if the bare-symbol introspection check returns `None`.
2. **Introspection path** (slash command, e.g., `/sig add-i64`).
   Entry: `handle_sig` (`src/session_v4.rs:2268`) → direct
   `current_symbol_table().get(name)` lookup → `format_entry_sig`.
3. **Call path** (bare symbol in head position, e.g., `(add-i64 2 3)`).
   Entry: `process_single_form` → typechecker + codegen, which goes
   through the normal name-resolution in `cranelisp-typecheck`.

## 3. Divergence point

The introspection path (2) and call path (3) both converge on the
current module's symbol table, which after prelude-load contains
re-exported `primitives` names like `add-i64` (per `spec/08-modules.md
§8.9` and §8.8.1 — implicit prelude import seeds the user module).

The bare-value path (1) also reads `current_symbol_table()` at
`src/session_v4.rs:2202`:

```rust
let entry = {
    let guard = self.current_symbol_table();
    guard.get(name)?.clone()
};
```

So the lookup finds a `ModuleEntry`. After `resolve_entry_for_display`,
the match block at line 2211 inspects the resolved entry. For a
primitive re-exported from `primitives` the resolved entry is a
`ModuleEntry::Def { kind, scheme, .. }` where `kind` is likely
`DefKind::Primitive` or similar.

**Suspect divergence**: the match arm at line 2226 for
`ModuleEntry::Def` is reached, but the returned `FQSymbol` uses
`module: self.current_module_path()` — i.e., `user`, not `primitives`.
Then when the downstream display formatter looks up the value for
rendering, it looks under `user/add-i64`, which does not exist (the
value lives under `primitives/add-i64`).

Alternatively, if `check_bare_symbol_introspection` returns `None` for
some primitive kinds, the bare-value path falls through to
`process_single_form`, which routes through the typechecker. If the
typechecker resolves `add-i64` to a constrained/polymorphic scheme, it
may reject the bare reference with the same error the caller sees
(`undefined variable`).

The diagnosis is one of these two; Slice 1's isolation step picks the
one that matches behaviour.

## 4. Fix

**Single-site alignment** in the bare-symbol handler. The fix direction
depends on which divergence holds:

- **If the issue is `FQSymbol.module` incorrect** in
  `check_bare_symbol_introspection`: use `resolved_module` (the
  second return of `resolve_entry_for_display`) as the `FQSymbol.module`,
  not `self.current_module_path()`. Re-export provenance is already
  tracked per `spec/08-modules.md §8.9` — line 273 requires
  introspection to display the original defining module.
- **If the issue is fall-through to typecheck with a rejected bare
  reference**: widen `check_bare_symbol_introspection`'s match to
  cover the primitive kind(s) currently returning `None`, ensuring
  the bare symbol produces an `EvalResult::Def` directly (matching
  `/sig`'s output shape — see §5 below).

Both candidate fixes are within `session_v4.rs`. No boundary-type
change. No `SymbolInfo` / `ModuleEntry` shape change.

## 5. Expected output

Per `repl/spec.md §1.1` universal format: `:Type name ; classification
- docstring`.

For `add-i64` at the prompt, expected:

```
:(Fn [Int Int] Int) primitives/add-i64 ; primitive - (add-i64 a b) returns a + b
```

Matches the introspection path's output shape. Slice 1's success
criterion is that path 1 and path 2 produce the same output string
(modulo slash-command prefix).

## 6. Cross-references

- `repl/spec.md §1.1` — universal `:Type name ; classification -
  docstring` output format (normative for the bare-value path).
- `spec/08-modules.md §8.9` — re-export provenance: introspection MUST
  display the original defining module (`primitives/add-i64`, not
  `user/add-i64`).
- `spec/08-modules.md §8.8.1` + §8.9 primitives paragraph (line 544) —
  primitives are brought into user scope via the implicit prelude
  import as bare names; this is spec-expected behaviour.
- `design/int/dual-path-persistence-collapse.md` — the "two paths
  must not diverge" anti-pattern Sprint 59 established; bare-value vs
  introspection vs call is a third instance.
- **Decision 22** (`defined_symbols()` predicate, if the divergence
  turns out to be in which symbol-filter the bare-value handler
  consults) — the fix aligns all three paths on the same filter.

## 7. Testing approach

`/qa` authors a narrow integration test in `tests/` that launches a
REPL subprocess, types `add-i64` (newline-terminated), and asserts
stdout contains the expected type-annotated qualified name. Slice gate:
5 consecutive runs at 0 failures.

Covered symbols in the same test or sibling tests: `add-i64`,
`eq-i64`, `mul-i64`, `sub-i64`, `int-to-string`, `str-concat` — a
sample from the re-exported primitives surface.

## 8. Spec implication (possible)

If isolation reveals that re-exported primitives have spec-divergent
value-position semantics (allowed at call-position, disallowed at
value-position), file `FIXME(/spec)` on `spec/08-modules.md §8.9` with
the observed gap. Spec currently treats re-export as making the name
part of the re-exporting module's public API (line 271) — no explicit
value-vs-call distinction. If the defect turns out to be a spec gap
rather than an implementation divergence, the fix scope shifts to
`/spec` and Slice 1 may carry to a later sprint with the gap
documented.

Unlikely (§8.9 line 273 treats re-exports as first-class public
names), but flagged for completeness. Unfiled until diagnosis confirms.

## 9. No boundary-type changes

Per `/arch` Phase 2 review: Slice 1 is a single-site alignment inside
`src/session_v4.rs::eval_v4`. No `SymbolInfo`, `ModuleEntry`,
`FQSymbol`, or introspection-type shape changes.

## 10. Sketch comparison

Per `CLAUDE.md §"Sketch Oracle"`. The sketch REPL (`sketch/src/repl.rs`
`run_repl_loop`, l.1868; dispatch at l.1941 `parse_repl_command`) has
a single-threaded eval path: colon commands branch to `handle_command`,
everything else funnels through one compile-and-execute route without
a dedicated bare-symbol-value handler — a bare symbol is a 0-arg
expression and flows through the same typecheck + codegen as any
other expression. No three-path split exists to diverge. The
reimplementation's bare-value vs. introspection vs. call split emerged
from the v4 persistent-worker / `CompilerSession` restructure where
`check_bare_symbol_introspection` was added to produce the
spec-mandated introspection card (`repl/spec.md §1.1`) without a round
trip through codegen. The divergence is incidental to that
restructure, not a re-discovered sketch pattern. See
`design/int/dual-path-persistence-collapse.md` for the broader class
of anti-pattern this is an instance of.
