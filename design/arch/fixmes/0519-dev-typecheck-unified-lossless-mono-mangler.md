---
number: 0519
target: /dev
filed_by: /arch
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-typecheck/src/traits/monomorphise.rs:1034 (build_mangled_name), :1062 (concrete_type_name), :146/:375/:787 (mangler callsites), :539 (register_mono_entry); crates/cranelisp-typecheck/src/program.rs:665 (mangle_sig), :675 (mangle_type), :3469 (seen-dedup key hand-roll), :3507 (fn-value mangle); design/arch/interfaces.md §"Mono-instance linker identity is lossless by construction"; design/arch/principles/07 + /20; design/backend/ownership-codegen.md §13.3 Ruling 1
status: open
---

# Unify the mono-mangler onto one lossless, home-qualified, recursive key (cures 0483 + 0508)

## Crate

`cranelisp-typecheck` (`/dev` narrow-deployed to typecheck). No `cranelisp-types`
edit, no backend edit. This FIXME is B3.1b in the S102 Wave-11 split.

## Issue — the mangler is lossy along TWO axes and mirrors a lossless sibling

`build_mangled_name` (`monomorphise.rs:1034`) via `concrete_type_name` (`:1062`)
drops distinguishing information from a mono instance's name:

- **ADT type-args erased** — `concrete_type_name` returns only `fqtn.name` for
  `Type::ADT(fqtn, args)` (`:1068`). So `apply2@(Vec Int)` (params
  `[Fn, (Vec Int), Int]`) and `apply2@(Vec String)` both mangle to
  `apply2$Vec+Int` (the `Fn` param is `filter_map`-dropped, the `Vec` arg
  erased). `register_mono_entry` (`:539`) inserts under `mono.defn.name` (the
  mangled name); the second insertion reuses the first's `got_slot`
  (`existing_got_slot`, `:564`) and overwrites the body → two distinct
  instantiations COLLAPSE to one body/slot/GOT-entry. **This is 0483's
  CLIF-proven root cause** (the surviving String-typed heap elem-dec runs on
  Int payloads `10/20/30` → `vec_drop(v, heap_dec)` → SIGBUS). Not a backend
  `fn_as_value` wrapper defect — the colliding symbol is the HOF's own upstream
  monomorph.
- **Home erased** — the name is `{bare_fn_name}${types}`, home-independent. Two
  same-named imported generics `a/iden2` and `b/iden2` at one arg type both mint
  `iden2$Int` in the consumer → silent wrong-dispatch (**0508**).

Both are the SAME bug: `build_mangled_name` dropping distinguishing facts. The
`debug_assert!(is_concrete())` tripwire (`:1046`) misses both — both types ARE
concrete; concreteness ≠ mangle-distinctness.

**Principle-7 mirror.** `program.rs::mangle_type` (`:675`) is a SECOND mangler
for the same job (multi-sig variant naming) that does ADT args CORRECTLY
(recurses → `Vec$Int` ≠ `Vec$String`). And `program.rs:~3469` hand-rolls a THIRD
mangle for the `seen`-dedup key (`format!("{}${}", fn_name, Display-of-types)`) —
which is home-blind (so it collapses the 0508 two-home case at the dedup step)
and disagrees in structure with `build_mangled_name`. Three manglers, one job,
mutually inconsistent.

## Resolution — one canonical, total, home-qualified mangler

**Mandated mangled-name grammar:**

```
{home}/{bare}${recursive-concrete-sig}
```

- **`home`** = the DEFINING module's `ModuleFullPath`. Use the `home:
  Option<&ModuleFullPath>` already threaded through `monomorphise_call`
  (FIXME 0355) when `Some` (imported generic); else `state.current_module`
  (local fn). Available at every callsite (`:146`, `:375`, `:787`, and the
  fn-value path `:3507`/`:3520` which carries `home` in its tuple). This
  distinguishes `a/iden2` from `b/iden2` → cures 0508.
- **`recursive-concrete-sig`** = each concrete param type mangled by a **total**
  type-mangler that recurses into EVERY concrete `Type` variant:
  - `ADT(fqtn, args)` → recurse into `args` (`Vec$Int` ≠ `Vec$String`) → cures 0483.
  - `Fn(params, ret)` → recurse into params + ret (do NOT `filter_map`-drop it;
    dropping the `Fn` param is a latent third collision axis — two instantiations
    differing only in a concrete `Fn`-typed param would collide. Present a token
    plus its recursed arg/ret structure).
  - `TyConApp`, scalars — as today, but present as distinguishing text.
  - The existing concrete param types stay (the sig is still the param vector).

**Collision-free BY CONSTRUCTION (Principle 20):** the name is a pure function
of (defining home, bare name, recursively-mangled concrete sig). Two
instantiations differing in any one fact mint different names; the "two distinct
instantiations → one name" state is unrepresentable. **Cache-safe (Principle 20
/ pure-function-of-persisted-facts):** all three facts are persisted (module
path, symbol, concrete param types) and compile-order-independent.

**Single-source it (Principle 7).** Author ONE canonical type-mangler
(totalize `program.rs::mangle_type` — it is the closer-to-correct mirror, already
recursing ADT args — by making it recurse `Fn` too) and ONE canonical
name-composer (`{home}/{bare}$sig`). Then:

- `build_mangled_name` becomes the home-qualified name-composer over the shared
  type-mangler (or is deleted in favour of it); `concrete_type_name`'s lossy
  `filter_map` is DELETED — the total mangler replaces it.
- `program.rs::mangle_sig`/`mangle_type` route through the same canonical mangler.
- The `seen`-dedup key hand-roll at `program.rs:~3469` routes through it too
  (else the dedup grain disagrees with the name grain — the 0508 collapse point).

Verify no consumer parses the mangled name structurally — it is opaque at every
crate boundary (produced in typecheck; consumed by name only through GOT-slot
dispatch and the linker). If a consumer splits on `$` or `/`, flag it (the `/`
in `{home}/…` and `/`-bearing module paths must not be mis-split — mirror the
`split_qualified` non-empty-remainder guard).

## Cache / schema cascade (SAME change-set)

The mangled name is the symbol-table entry key and is persisted as the
`.meta.json` entry identity. Changing the grammar changes on-disk identity → a
stale cache would mis-resolve. **Bump `CACHE_SCHEMA_VERSION`**
(`crates/cranelisp-backend/src/cache/mod.rs:236`, currently `12` → `13`) in the
same change-set. No `public-api.txt` move (the mangled name is an opaque
`String`/`LinkerSymbol`, not a signature-visible boundary type;
`build_mangled_name`/`concrete_type_name` are `pub(crate)`, `mangle_type`
private). No `cranelisp-types` edit.

## Failing-cell-first implementation + flip record

Write the failing cells FIRST (they are RED on HEAD), then land the mangler so
they flip green in the same change-set:

- **0483 e2e guards (already authored, RED on HEAD, /qa-owned)** —
  `tests/vec_query_value_use.rs::vec_get_as_value_two_instantiations_of_one_hof_repl`,
  `…_run_mode`, `vec_get_and_vec_push_as_values_through_one_hof_run_mode`. These
  are the flip record for the ADT-arg axis; they turn green when two
  instantiations mint two distinct bodies/slots. (Controls
  `vec_len_as_value_two_instantiations_of_one_hof_control` etc. stay green.)
- **Unit cells (yours, in `traits/monomorphise/tests.rs`)** — pin the grammar
  directly: `apply2@(Vec Int)` and `apply2@(Vec String)` mint two DISTINCT
  mangled names with distinct GOT slots; a `Fn`-typed param contributes
  distinguishing text; the home component differs for two same-named imported
  generics. The S102 0497 de-pool already added a `build_mangled_name` matrix
  (`two_instantiations_mint_two_distinct_concrete_mono_entries`,
  non-concrete-`Var` tripwire) — extend it for the ADT-arg + home + Fn axes.
- **0508 guard is /qa's to author** — the two-same-named-imported-home failing
  e2e repro is the `/qa` half of FIXME 0508 (kept open for exactly this). Your
  mangler fix makes it pass; coordinate so the repro exists to flip. Do NOT wait
  on it to land the fix — the unit cell for the home axis is your mandatory guard.

## Scope boundary — this is B3.1b; B3.1a is genuinely-backend and independent

This FIXME (B3.1b) needs NOTHING from the backend: once names are distinct, the
EXISTING concrete-mono codegen path compiles two distinct bodies/slots — no
backend change is required for 0483 to flip (CLIF-proven by the Wave-11
investigation). The `debug_assert!` tripwire keeps its job (residual `Var` →
clean type error, not a collision). Do not touch the backend `fn_as_value` seam.

The genuinely-backend residue (**B3.1a**, a separate /dev(backend) change-set) —
curry-glue `get_name` idempotency (ledger item 25), the Ruling-2 COW consumed-
source polarity contract (0474×3), the item-26 generic-Vec temp leak, and
Ruling-3 finalize — needs nothing from this mangler. The two halves are
independent and may land in either order (serial-source-touch rule applies; no
dependency edge).

## §13.3 correction (routed to /backend via /sprint, not editable here)

`design/backend/ownership-codegen.md` §13.3 Ruling 1 currently reads 0483 as a
backend wrapper-identity cell ("0483's defect class is precisely a wrapper-
identity cell"). That attribution is WRONG: the colliding symbol is the HOF's
own upstream typecheck monomorph, not the backend wrapper. Ruling 1's
wrapper-identity SCHEME (`__d24wrap_{fq}_{slot}__` / `__inlwrap_{bare}_{sig}__` /
re-keyed curry) is a valid durable convention and stands — but it does NOT fix
0483; the mangler (this FIXME) does. /sprint routes the §13.3 edit to /backend:
strike the 0483 attribution, keep the scheme as hygiene, and note that any
sig-in-a-wrapper-name must use the same total grammar mandated here (else the
mirror re-opens one level down). The §13.3 "investigation pin" WORKED — it
directed /dev to root-cause before fixing, which surfaced this.
