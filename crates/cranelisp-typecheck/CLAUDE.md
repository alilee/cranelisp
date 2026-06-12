# cranelisp-typecheck — local conventions

The voice of the code: API gotchas, data-structure invariants, debugging hooks
for the inference engine, traits, monomorphisation, and module-locality
resolution. Owned by `/dev` when narrow-deployed to this crate.

## Bare-name resolution & the implicit-prelude OUTER SCOPE (S78 §2)

The prelude is an **outer scope**, not flattened into each module's table
(`memory/project_prelude_outer_scope.md`). Every bare-name chokepoint roots at
`state.current_module` first and, on an inner miss, retries against the
`prelude` module **iff** the module's `PreludeFallback` bit is ON.

- **`PreludeFallback`** = `DashMap<ModuleFullPath, bool>` carried on
  `TypeCheckEnv.prelude_fallback`. Absence-is-OFF (`§2.7.1`). The single gate is
  `prelude_fallback_target(current_module) -> Option<prelude_path>`: returns the
  prelude path only when the bit is ON **and** `current_module != prelude` (a
  module never falls back onto itself).
- **I-1 public-only discipline**: a private prelude binding must NOT leak as a
  bare name. Reachability is judged relative to the *original* user
  `current_module` (never in prelude's subtree), so the rule reduces to
  `is_public()` on the prelude **head** entry. Filter the prelude-hop head on
  `prelude_terminal_visible` (== `is_public()`) BEFORE chain-following.

The chokepoint family (all in `checker.rs`):
`resolve_current_or_prelude` (the `resolve`-based value/type/trait/ctor family),
`probe_current_or_prelude` (chain-follow value/scheme + entry family),
`resolve_entry_in_current_module`, `resolve_terminal_entry_or_prelude`
(trait-method/impl-discovery), plus the two **constructor** chokepoints
threaded for FIXME 0317:

- **`lookup_constructor_type_with_state`** — the pattern-ctor `exists` gate (used
  by `infer.rs::lookup_constructor_scheme`). Falls back to prelude; filters the
  prelude head on `prelude_terminal_visible` before reading the parent type.
- **`is_internal_constructor_check_with_state`** — the internal-ctor reject gate
  (used by `infer.rs` value position + `check_constructor_pattern`). After the
  current-module gate misses, it re-resolves via the already-fallback-aware
  `resolve_entry_in_current_module` and reads `internal` off the **terminal**
  `DefKind::Constructor`. **GOTCHA**: `Bind`/`Pure`/`Effect` are registered
  `Visibility::Public` in `primitives` — the I-1 public filter must NOT hide
  `Bind`. What rejects `Bind` is its `internal: true` Constructor discriminator,
  reached *through* the fallback, NOT its visibility.

Rule of thumb when adding a new bare-name path: root at `current_module`, and on
an inner miss consult `prelude_fallback_target` + the public-head filter. Never
add a name-key shortcut to primitives; primitives reach user code only *via*
prelude's `(export [primitives [*]])` re-export, chain-followed through the
fallback (the §2 structural-not-skip guarantee).

## Module-locality (Principle 17)

Short-name lookup is current-module-only, with per-symbol chain-follow on
`Import`/`Reexport` entries (`source.module` references). No closure walk, no
universe scan. `resolve_terminal_entry_and_home` / `chain_follow_to_home` are
the navigation primitives; staging-aware via `probe_module_entry_owned`
(FIXME 0179 — staging shadows live when `module_path == staging.module`).

## Testing

Unit tests live in-crate (`#[cfg(test)]`), driven by `TestFixture`
(`checker/test_support.rs`). `TestFixture::new()` seeds the full synthetic world
(`FixtureBuilder::full()` — special forms, builtin type names, macros Sexp/SList,
the `IO` ADT with `Pure`/`Effect`/`Bind`-internal, Ring 0/1/3 primitives) built
on `cranelisp-types` only (no `cranelisp-primitives` dep). Seed the
`prelude_fallback` bit directly (`tf.prelude_fallback.insert(module, true)`) to
exercise the outer-scope fallback. Registering a type def with typed fields in a
bare module needs the field types reachable there — use **nullary** ctors in
prelude-resident test ADTs to avoid an `Int`-not-in-scope setup failure.
