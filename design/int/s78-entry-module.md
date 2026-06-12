# S78 — Entry-module de-special-casing (target design)

**Status:** AUDIT-FIRST TARGET DESIGN — for user sign-off. NO code/test changes enacted. §2 reshaped to the **settled** prelude-as-outer-scope model (user, 2026-06-11) + blast-radius walked.
**Owner:** `/arch` (Compiler Architect), Phase-5 PIVOT pass (2026-06-10) + settled-model §2 reshape (2026-06-11).
**Sibling:** `design/int/s78-implementation.md` (the in-call-stack restructure — landed + verified sound). This doc addresses the **disease** behind that restructure's `/review` B1 finding: the **entry module** has accreted special-casing it should not have.

---

## 0. Overview — the one principle, four manifestations, one orchestration defect

**The principle.** No module gets special treatment except the synthetic modules (`primitives`, `platforms`, `macros`) and `prelude` (the single implied import). The synthetics are compiler-seeded; `prelude` is the one import every user module implicitly receives (spec §8.8.1, §5.9, §11.2). Every other module — including the **entry module** (the `main`-bearing module under `--run`, or the REPL's current target) — is an ordinary module.

**The misconception the implementation encodes.** `"user"` is treated as a privileged, always-present module. It is not: `"user"` is **only the default CLI name** when the user passes no target. Most programs compile a differently-named entry module (`sudoku.cl` → entry module `sudoku`); those programs have **no `user` module at all**. Every hardcoded `"user"` in int is therefore either dead (the real entry registration is name-agnostic — §1) or a latent bug for non-`user` entry programs (§2, §3).

**Four hardcoded-`"user"` manifestations + one orchestration defect** (the disease /review B1 is a symptom of):

| # | Site | What's wrong | Section |
|---|---|---|---|
| 1 | `session_v4.rs:1005–1013` ctor pre-seed of `"user"` + **stale comment** | Pre-seeds a `"user"` symbol table with a comment claiming `register_builtins` registers special forms "on it" — but special forms mount at **root `""`** (`bootstrap.rs:295`). The pre-seed is (near-)vestigial. | §1 |
| 2 | `imports.rs:311` `is_seeded` name-skip (`m == "user" \|\| "primitives"`) | S76 W2 hack (`d62db12`). Skips §8.6.4 ambiguity for `user`/`primitives`-sourced imports. **No spec basis** — the real scar is **flattening prelude into the inner table**; only `prelude` is implied (as an outer scope), and primitives reach user code *via* prelude's re-export through the same fallback. Deletes with the flattening. | §2 |
| 3 | `session_v4.rs:2682` `handle_mod("")` → `"user"`; `session_v4.rs:1154` `current_repl_module` default; `session_v4.rs:4559` FQ-parse default | Hardcode `"user"` where they mean **the entry module**. | §1.3 |
| 4 | Dual-orchestration of the entry/REPL module (`/review` B1) + **false invariant** `scheduler.rs:89–97` | The entry module is BOTH eval-thread-driven (`process_single_form`) AND pool-claimable (registered with `sexps: Some`, requeued by `try_unblock_locked`). Two actors on one module — the exact in-progress-sharing class the S78 restructure removed, relocated to `ModuleState.sexps`. | §3 |

**Doc map.** §1 = entry-module-as-first-class concept + the pre-seed vestigial verdict. §2 = the **prelude-as-outer-scope** import model (replacing `is_seeded`) + its **blast radius** (§2.5) + the `/imports` presentation decision (§2.6). §3 = single-orchestration for the entry module. §4 = expunge list (docs/comments). §5 = disposition, sizing, Principle recommendation. §6 = open items needing sign-off.

**Dependency on `/spec`.** §2's outer-scope model is grounded in spec §8.6.4 (explicit imports shadow the implicit prelude *"just as inner `let` shadows outer"* — scope layering). /spec proposes sharpening §8.6.4/§8.8 to make prelude-as-outer-scope normative (vs. the current flattened-with-shadow-exception phrasing) — **pending user sign-off**. The model is settled by the user (2026-06-11); the /spec wording is editorial alignment, not a model decision. **No `cranelisp-types` change is needed for §2** (the prior provenance-marker proposal is rejected — see §2).

---

## 1. Entry-module concept — first-class, name-agnostic

### 1.1 The concept

An **entry module** is the module the session is asked to compile and run: the `main`-bearing module under `--run`/`--link`, or the REPL's initial current target. It is named by the CLI target (`sudoku`, `myapp`), defaulting to `"user"` only when no target is given (fresh REPL, `cranelisp` with no file). It is an **ordinary module in every respect** — it receives the implicit prelude (as an outer-scope fallback, §2), it is subject to §8.6.4 ambiguity within its own (inner-scope) table, it has a normal symbol table, and it is orchestrated like any other module. Its only distinction is *role* (it holds `main` / is the REPL cursor), not *mechanism*.

### 1.2 The real registration is already correct (name-agnostic)

The entry module is created by the **root compile call**:

- `main.rs:172`: `s.register_module(entry_module_name)` — name-agnostic; `entry_module_name` is the CLI target.
- `session_v4.rs:1905 register_module` → `register_entry_module` (`session_v4.rs:3626`) → resolves the file (or empty source for a fresh REPL) and calls `register_module_with_source(module_name, …)` → `scheduler.register_module(module, sexps, false)`.

This path is **correct and requires no change**. It registers by the real entry name, seeds its symbol table lazily via `cranelisp_types::ensure_module_exists` / `SessionSymbolTable::new_with_params` on first touch (the scheduler `ModuleState` carries the sexps; `process_cluster_once` runs against a table created on demand). Nothing here hardcodes `"user"`.

### 1.3 The constructor pre-seed verdict — VESTIGIAL, deletable (with one check landed)

`session_v4.rs:1005–1013` pre-seeds a `"user"` symbol table in `CompilerSession::new`, *before* `mount_synthetic_modules` and *before* any entry registration. Its comment (line 1007) claims it must precede `register_builtins` "which registers special forms on it."

**Verdict: the comment is stale and the pre-seed is vestigial.** Verified against source:

1. **Special forms mount at root `""`, not `"user"`.** `bootstrap.rs:293–295 register_special_forms` inserts `ModuleEntry::SpecialForm` into the root module `""`. The pinned test `mounts_special_forms_at_root` asserts this. The pre-seed is NOT load-bearing for special forms — the comment describes a mechanism that does not exist.

2. **`register_builtins` no longer exists.** It was reconstructed as `mount_synthetic_modules` (`bootstrap.rs`, FIXME 0242). That function seeds special forms (root `""`), `primitives`, and `macros` — it does **not** require a pre-existing `"user"` table. Its own comment (`session_v4.rs:1055–1056`) says "`primitives` and `user` are already mounted above; this only adds to them + creates `macros`" — but inspection of `mount_synthetic_modules` shows it touches `primitives`/`macros`/root, never `user`. The "adds to user" claim is also stale.

3. **`current_repl_module` + `repl_check_state` reference `user_module`** (`session_v4.rs:1154–1155`). These are the only *other* consumers of the pre-seeded `user_module` local. They are §3-relevant (REPL cursor) but do **not** require the symbol table to be pre-seeded — `process_single_form` calls `ensure_module_exists` (`session_v4.rs:2268`) on every form, creating the table on demand for whatever the current module is.

4. **`TestRunnerState.current_module` is initialised to `user_module`** (`session_v4.rs:1078`) — again a default-name choice, not a table-existence dependency.

**Minimal replacement.** None for the symbol-table pre-seed itself — delete `session_v4.rs:1010–1013` (the `symbol_tables.insert(user_module, …)` call) outright. The lazy-create path (`ensure_module_exists` / the entry registration) covers every reader. The `current_repl_module` / `repl_check_state` / `TestRunnerState.current_module` initial values should reference **the entry module name passed to the session**, not a hardcoded `"user"` — see below. (Today the session constructor does not receive the entry name; `register_module(entry_module_name)` is a *later* call. The clean target threads the entry name into `CompilerSession::new`, or defers `current_repl_module` initialisation to the entry registration. /dev picks the smaller diff; both are target-shaped. Default remains `"user"` when no target is given.)

> **/dev verification obligation (do at implementation, not now).** Before deleting `:1010–1013`, confirm by a build+REPL smoke that no path reads `symbol_tables["user"]` before the first `ensure_module_exists`. The candidates are: the REPL pre-first-input introspection commands (`/list`, `/imports` on an empty session) and `mount_synthetic_modules`'s "adds to user" comment (verified false above, but re-grep `mount_synthetic_modules` for any `"user"` literal). If a pre-first-input REPL command needs the entry table, replace the pre-seed with a single `ensure_module_exists(&symbol_tables, &entry_module)` keyed by the **real entry name** — create-lazily-by-real-name, never the hardcoded literal.

### 1.4 The three hardcoded-`"user"` defaults (#3)

These three sites hardcode `"user"` where they mean *the entry module*:

- `session_v4.rs:2682` — `handle_mod("")` (`/mod` with no arg) returns to `"user"`. **Target:** return to the **entry module** (the session's entry name). `/mod` with no arg means "back to the home module," which is the entry module, not necessarily `user`.
- `session_v4.rs:1154` — `current_repl_module` initialised to `user_module`. **Target:** the entry module name (§1.3).
- `session_v4.rs:4559` — `run_test_by_name` FQ-parse: an unqualified test name defaults its module to `"user"`. **Target:** the entry module (or the REPL's current module — `run_test_by_name` runs in REPL/`--run` test discovery; the right default is the current REPL module, already tracked). For a non-`user` entry program this currently mis-routes unqualified test lookups to a non-existent `user` table.

All three reference a single session-held **entry-module name** (or `current_repl_module` where the *current* cursor is the right referent, as in `/mod` and test-by-name). No hardcoded `"user"` literal survives in orchestration logic; `"user"` survives **only** as the CLI default in `main.rs`'s argument parsing (where it belongs — it is the default *name*, the one legitimate use).

---

## 2. Import model — prelude is an OUTER SCOPE (scope-layering fallback)

> **Model settled by the user (2026-06-11).** The implicit prelude is an **outer scope resolved by a symbol-lookup fallback** — it is NOT materialised (flattened) into each module's symbol table. The provenance-marker design (prior §2.3a) and the install-order design (prior §2.3b) are both **REJECTED**: they were realizations of a *flattened-with-shadow-exception* model that does not match the spec's scope semantics. The settled model needs **no `cranelisp-types` change** and **no per-symbol marker**.

### 2.1 The defect, and why a flattened model produced it

`imports.rs:311 is_seeded` skips §8.6.4 ambiguity detection for any import whose source module is `"user"` or `"primitives"`:

```rust
let is_seeded = |entry| matches!(entry, Import { source, .. }
    if source.module == "user" || source.module == "primitives");
if is_seeded(existing) || is_seeded(&new_entry) { continue; }  // skip ambiguity
```

This is a **name-keyed hack** (S76 W2, `d62db12`, comment "seeded builtins take priority") with no spec basis. The deeper cause: the implicit prelude was being **flattened** into each module's table as a set of `ModuleEntry::Import { source: prelude/… }` bindings, sitting *in the same table* as the module's own defs and explicit imports. Once prelude lives in the inner table, an explicit import (or a redefinition) of a prelude-provided name collides with the flattened prelude entry, and §8.6.4 ambiguity fires where it must not — so a name-keyed skip was bolted on to paper over the collision. The scar is the flattening; `is_seeded` is the bandage over the scar.

### 2.2 The settled model — prelude is the OUTER scope

Spec §8.6.4 already states the mechanism: explicit imports shadow the implicit prelude *"just as inner `let` bindings shadow outer ones."* **That is scope layering, not a flattened table with a shadow-exception.** Two scopes, consulted in order:

- **Inner scope = the module's own symbol table.** Its local definitions and its *explicit* imports/exports only. **Prelude bindings are NOT in this table.** This is the scope §8.6.4 ambiguity (`Ambiguous` poisoning) operates over — wholly unchanged.
- **Outer scope = the `prelude` module's own table.** Consulted **only on a resolution miss** in the inner scope. This is a *fallback*, not a copy.

Every consequence falls out **structurally** — there is no special rule, no precedence axis, no tier marker:

1. **Explicit/local shadows prelude automatically.** Inner is consulted before the outer fallback. The shadow is a lookup ordering, not a same-table override.
2. **Explicit-vs-explicit §8.6.4 ambiguity is unaffected.** Both colliding entries live in the inner table; the fallback never enters the picture. `Ambiguous` poisoning is exactly as today.
3. **No `is_seeded` name-check, no per-symbol provenance marker, no `cranelisp-types` change.** The flattening that *created* the collision is gone, so the bandage deletes with it. `imports.rs:311–317` is removed; `insert_detecting_ambiguity` reverts to uniform `Ambiguous` on any two indirect entries from different sources.
4. **Primitives reach user code via prelude's re-export, resolved through the same fallback.** Prelude does `(export [primitives [*]])` → `add-i64` etc. are Public bindings in prelude's *own* table (`imports.rs:453–494` proves the shape). A user reference to `add-i64` misses the inner table, falls back to prelude, and chain-follows prelude's `Import`→primitives edge to the canonical entry (Decision 0048 uniformity). No per-module primitives seeding exists or is needed.

### 2.3 The one per-module bit — prelude-fallback ON/OFF

The fallback is **per-module**, gated by exactly the condition that gates implicit-prelude *injection* today (`inject_prelude_if_needed`, spec §8.8.1 "module does not reference prelude"):

- **ON (default):** the module did not refuse/reference prelude → bare-name misses fall back to the prelude scope.
- **OFF:** the module references prelude — `(import [prelude []])` (explicit refusal) or any selective `(import [prelude [foo bar]])` (the named bindings land in the inner table as ordinary explicit imports; no implicit fallback). `sexps_reference_prelude` (`worker.rs:3133`) is the existing predicate; the bit is just its negation, recorded per module.

The synthetic `prelude` module itself, and any module that references prelude, have the bit OFF — identical to today's injection gate (`inject_prelude_if_needed` early-returns for `*module == "prelude"` and when `sexps_reference_prelude` is true). **One bit per module, set where injection is decided.** It rides the module's session state (the natural home is the `SymbolTable` itself — a `prelude_fallback: bool` field, or session-side keyed by module path; /dev picks the smaller diff, both int-internal).

### 2.4 What changes vs. what stays

- **Stays:** prelude *discovery* and *loading* — `inject_prelude_if_needed` still resolves the prelude file, registers it as a dep, and drives it to readiness (the module must exist for the fallback to consult). Only the **flattening** is removed.
- **Changes:** instead of `install_imports([glob_spec("prelude")])` (flatten), `inject_prelude_if_needed` **sets the per-module fallback bit ON** and ensures prelude is loaded. The bit is consulted at every bare-name resolution miss (§ blast radius below). `is_seeded` and the prelude-glob install both delete.

This is the **faithful implementation of the spec's scope model** — not a performance optimization, not a tier-precedence scheme. The module table stops holding prelude symbols; resolution gains an outer-scope fallback.

### 2.5 BLAST RADIUS — every bare-name resolution site needing the prelude fallback

The module table stops holding prelude symbols, so every site that resolves a **bare (unqualified) name by direct current-module lookup** must gain "miss → consult prelude (gated by the fallback bit)." Qualified `mod/sym` references are **unaffected** — they name their module directly and never relied on flattening. The walk groups the sites by crate. **No `cranelisp-types` change** is required anywhere — the fallback is realized at the *callers* of the shared `cranelisp_types::resolve` (by constructing a two-hop view or retrying against prelude), never inside the primitive.

#### A. Typecheck name resolution (`cranelisp-typecheck`) — primary consumer, TWO chokepoints

Bare-name resolution in typecheck funnels through two primitives, both keyed on `state.current_module`:

1. **`probe_module_entry_owned(current_module, name)`** — `checker.rs:979`. The chain-follow family's single entry point. Backs:
   - `lookup_in_current_module` (`checker.rs:966–969`) → `lookup` (`checker.rs:898–955`, the value/scheme path: env stack → **current module** → qualified).
   - `resolve_terminal_entry_and_home(current_module, …)` (`checker.rs:1098–1105`) → `resolve_entry_in_current_module` (`checker.rs:1081`), the **entry**-returning path (constructors, trait decls, type defs). Callers: `infer.rs:234,253,571,811`, `traits.rs:1553,2014`, `checker.rs:307,1431,1566`.
   This is a **single chokepoint** for the whole chain-follow family: add the fallback inside `probe_module_entry_owned` — when `module_path == current_module` (the bare-name case) and the probe misses AND the module's fallback bit is ON, re-probe against `ModuleFullPath::from("prelude")` and chain-follow from there. Every caller above inherits the fallback for free. (Probes of an *explicitly named* module — `resolve_fq_symbol`, the `fq.module` arm — must NOT fall back; the fallback fires only for the `current_module` bare-name probe.)

2. **`cranelisp_types::resolve(... first_hop ...)`** — the shared resolver's unqualified branch (`resolve.rs:280–287`, `first_hop.lookup(name)`). Called from **six sites** in `checker.rs`: `:726` (`resolve_type`), `:768` (`resolve_trait`), `:803`/`:844` (`resolve_constructor` family), `:1155` (`resolve_qualified`'s composed form — qualified, no fallback needed), `:1711` (`resolve_type_expr_in_module`). The `first_hop` view is built by `current_symbol_table(state)` (`checker.rs:416–432`). **Single chokepoint:** make the bare-name first-hop a *two-hop* view (current module, then prelude when the bit is ON) so `first_hop.lookup` transparently falls back — OR have each of the bare-name callers retry `resolve` against prelude on `TypeNotFound`/`TraitNotFound`/`ConstructorNotFound`. Phase 3 preferred the view-construction approach; **AS BUILT it was the caller-side retry** (`resolve_current_or_prelude`), because the shared `View` newtype carries at most two sources (staging+live) and a third prelude source would need a `cranelisp-types` view-type change — see §2.7.5 Chokepoint 2 AS BUILT. Either way: int-typecheck-local, **no change to `cranelisp_types::resolve` itself.**

   *Note:* `resolve_macro_head` (`resolve.rs:357`, called by int's `recognize_macro_head`) wraps the same `resolve` — a bare macro head provided by prelude (e.g. a prelude-defined `defmacro`) flows through the same first-hop view, so the view-side fallback covers macro recognition too with no separate change.

**Verdict (typecheck): two chokepoints, both localized** — `probe_module_entry_owned` (chain-follow family) + the `current_symbol_table`→`View` construction (the `cranelisp_types::resolve` family). The fallback bit must be readable in typecheck; it is set by int but consulted here, so it rides the per-module `SymbolTable` (the cleanest shared home — see §2.3) or the `TypeCheckEnv`'s module map. This is the primary blast-radius consumer.

#### B. The import installer (`src/imports.rs` + `src/worker.rs`) — localized

- **`inject_prelude_if_needed` (`worker.rs:3055–3129`)** — the gate. Replace its two `install_imports([glob_spec("prelude")])` calls (`worker.rs:3085`, `:3125`) with "set the per-module fallback bit ON"; keep the discovery + `register_dep` + `register_module` + `block_for_typecheck` drive (prelude must be loaded for the fallback to consult). `sexps_reference_prelude` (`worker.rs:3133`) already computes the OFF condition. **Single site.**
- **`insert_detecting_ambiguity` (`imports.rs:277–331`)** — delete the `is_seeded` closure + its use (`imports.rs:311–317`); two indirect entries from different sources revert to uniform `Ambiguous`. The visibility-upgrade branch (`:292–304`) and the directly-defined-takes-priority branch (`:326`) are unchanged. **Single site.**
- **Glob expansion (`collect_glob`/`collect_bindings`, `imports.rs:149–165`)** — *unchanged*. It still flattens *explicit* imports/exports into the inner table (that is correct — explicit imports ARE inner-scope). Only the *implicit prelude* glob stops flattening, and that is governed entirely by `inject_prelude_if_needed` not calling `install_imports` for prelude.

**Verdict (installer): localized** — one behavior change in `inject_prelude_if_needed`, one deletion in `insert_detecting_ambiguity`. The fallback bit is recorded by `inject_prelude_if_needed`.

#### C. REPL introspection (`src/session_v4.rs`) — `/imports` + `describe_symbol`

These enumerate / probe a module's table; prelude names won't be in it.

- **`handle_imports` (`session_v4.rs:2898–2992`)** — iterates `table.all_symbols()` for `ModuleEntry::Import` entries and buckets them (Macros/Traits/Types/Fns). Today prelude names appear because they are flattened `Import` entries; under the new model they vanish from this enumeration. **Presentation decision (see §2.6):** when the fallback bit is ON, additionally enumerate the `prelude` module's *own* public symbols and present them under a distinct `Prelude (implicit)` group, separate from the explicit-import categories. Special forms are already enumerated from root `""` separately (`:2916–2923`) — that path is unaffected. The filtered mode (`/imports prelude`) already enumerates by source module and would now show nothing from the inner table; it should enumerate prelude's own table directly. **Localized add** (one handler).
- **`describe_symbol` (`session_v4.rs:1451–1502`)** — backs `/sig`, `/doc`, `/info`, `/type`. Probes current-then-root (`:1458–1470`). A prelude-provided bare name (e.g. `/sig map`) currently hits the flattened `Import` in the current table; under the new model it misses both current and root. **Add a prelude hop** (gated by the bit) between current and root, mirroring the typecheck fallback, so `/sig`/`/doc` on a prelude name still resolve. **Localized add** (one method).
- **`list_user_definitions` (`/list`, `session_v4.rs:1507+`) — UNAFFECTED.** It deliberately skips `Import`/`Reexport` entries and shows only local `Def`s (`:1512–1514`). Prelude names were never in `/list`; the contract is unchanged.
- **`handle_exports` (`session_v4.rs:3035+`) — UNAFFECTED.** It enumerates a *named* module's own table by request; never relied on flattening into the current module.

**Verdict (introspection): two localized adds** (`handle_imports` prelude group + `describe_symbol` prelude hop); `/list` and `/exports` need no change.

#### D. Backend codegen — UNAFFECTED (FQSymbol/GOT-based)

Codegen resolves calls off the **resolved FQSymbol / canonical jit-name and per-module GOT**, not by re-resolving bare names against the importing module's table. The one site iterating tables (`jit.rs:110–157 register_platform_effect_symbols`) walks `symbol_tables.iter()` — *all* tables including prelude's own — and registers PlatformEffect symbols under the **defining (source) module's** canonical name + GOT slot (`jit.rs:143–149`). The prelude module's own table still carries its `Import`→primitives edges and GOT, so platform/primitive symbols remain discoverable whether or not they are flattened into the user table. After typecheck binds a bare name to its resolved `FQSymbol` (via the §A fallback), codegen emits the canonical name and loads the source-module GOT slot. **No flattened-prelude `Import` entry in the user table is load-bearing for codegen.** Confirmed unaffected.

#### Blast-radius summary

| Crate | Sites | Single chokepoint? |
|---|---|---|
| `cranelisp-typecheck` | `probe_module_entry_owned` (`checker.rs:979`) + `current_symbol_table`→`View` (`checker.rs:416`) feeding 6 `cranelisp_types::resolve` callers | **2 chokepoints**, both localized |
| `src/imports.rs` + `src/worker.rs` | `inject_prelude_if_needed` (set bit, stop flattening) + delete `is_seeded` | **localized**, 2 sites |
| `src/session_v4.rs` (introspection) | `handle_imports` (prelude group) + `describe_symbol` (prelude hop) | **2 localized adds**; `/list`,`/exports` unaffected |
| `cranelisp-backend` | — | **UNAFFECTED** (FQSymbol/GOT) |
| `cranelisp-types` | — | **NO CHANGE** (fallback at callers, not in the primitive) |

### 2.6 `/imports` introspection presentation decision

Today `/imports` lists prelude-provided names mixed into the Macros/Traits/Types/Fns categories (they are indistinguishable flattened `Import` entries). Under the outer-scope model the inner table holds only *explicit* imports, so the categories naturally narrow to what the module actually imported — which is **more honest** (the self-documenting-REPL principle: `/imports` should show what *this module* brought in).

**Decision: keep prelude names listed, but in a distinct group.** When the per-module fallback bit is ON, `/imports` appends a `Prelude (implicit)` section enumerating the prelude module's own public symbols, rendered with a clarifying comment (e.g. `; implicit — available via the prelude outer scope, shadowed by any explicit import/def of the same name`). Rationale:

- **Discoverability is preserved** — a user still sees `map`, `filter`, etc. are available, satisfying the self-documenting-REPL design principle.
- **The grouping makes the scope layering visible** — explicit imports (inner) are separated from prelude (outer), teaching the shadowing model the spec describes.
- **When the bit is OFF** (module refuses/references prelude) the group is absent — correctly reflecting that no implicit fallback is active.

This is strictly an int/REPL presentation choice; it has no spec consequence and is owned by `/int` (REPL experience per `/repl` spec). It is sized with the §2 introspection work (§5.2).

---

## 2.7 REALIZATION — fallback-bit home + cross-crate threading (the load-bearing pin)

> **This section pins the one genuinely-unpinned piece** (§6 open-item 4): where the per-module `prelude_fallback: bool` lives and the **exact channel** by which it reaches typecheck's two resolution chokepoints — so the `/dev (cranelisp-typecheck)` and `/dev (src/)` agents implement against one contract. The MODEL (§2.1–§2.6) is settled; this is its concrete wiring. **Source-confirmed against the working tree (2026-06-11).**

### 2.7.1 The home — a session-side companion `DashMap`, exactly parallel to `module_aliases`

`module_aliases` is the precedent and the template. Confirmed in source:

- **Type:** `pub type ModuleAliases = dashmap::DashMap<ModuleFullPath, ModuleAliasEntry>` (`crates/cranelisp-types/src/module.rs:419`). A session-level map keyed by `ModuleFullPath`.
- **Home:** owned on `SharedState` — `pub module_aliases: cranelisp_types::ModuleAliases` (`src/session_v4.rs:750`). int owns population; typecheck reads it **read-only**.
- **Threading:** carried into typecheck as `module_aliases: &'a ModuleAliases` on `TypeCheckEnv` (`checker.rs:204`), supplied via `TypeCheckEnv::new`/`new_with_staging` (`checker.rs:348,380`) and as the 4th argument to `check_forms(parsed, ctx, symbol_tables, module_aliases)` (`form.rs:83–88`). int threads `&self.shared.module_aliases` at every call site (`src/cluster.rs:216`, `src/worker.rs:288`, `src/session_v4.rs:2301/3228/3268/4464`).

**Decision: the fallback bit rides a companion map of identical shape, threaded through the identical channel.** Introduce (int-owned, in `cranelisp-types` as a *type alias only* — see the cranelisp-types note below):

```rust
// session-side, owned on SharedState alongside module_aliases:
pub prelude_fallback: dashmap::DashMap<ModuleFullPath, bool>,
```

- **Keyed by `ModuleFullPath`** — same key space as `module_aliases` and `symbol_tables`. A module path present with value `true` ⇒ fallback ON; absent OR `false` ⇒ fallback OFF. (Absence-as-OFF is the natural default: synthetic modules, `prelude` itself, and any prelude-referencing module are simply never inserted.)
- **Populated by int** in `inject_prelude_if_needed` (§2.7.3) — the one site that already decides the ON/OFF condition.
- **Read by typecheck** at the two chokepoints (§2.7.2), via a borrowed `&'a PreludeFallback` carried on `TypeCheckEnv` next to `module_aliases`.

**Why a companion map, not a `SymbolTable.prelude_fallback: bool` field.** `SymbolTable` is a `cranelisp-types` type; adding a `bool` field to it is a `cranelisp-types` *structural* change (touches serde/cache schema, every constructor, the `()`↔`<Code, ()>` flavour conversions). The companion map keeps the bit **session-side and out of the serialized symbol-table shape** — it is recomputed per session from source (`sexps_reference_prelude`), never cached. This is the §6 open-item-4 "session-side, cranelisp-types-free" fork, now **selected**. Confirmed: no field is added to any cached/serialized type.

### 2.7.2 The cranelisp-types question — type alias is NOT a structural change

The companion map's *type* (`DashMap<ModuleFullPath, bool>`) is naturally expressed as a `cranelisp-types` **type alias** living beside `ModuleAliases` (`module.rs:419`), so both int and typecheck name the same type without int↔typecheck depending on each other:

```rust
// crates/cranelisp-types/src/module.rs, beside ModuleAliases:
/// Session-level per-module prelude-outer-scope fallback flags (S78 §2.7).
/// `module_path → true` ⇒ bare-name inner-miss falls back to the `prelude`
/// module's table. Absent/false ⇒ no fallback. int populates; typecheck reads.
pub type PreludeFallback = dashmap::DashMap<ModuleFullPath, bool>;
```

**This is a type *alias*, not a new struct/enum/field on any existing type** — it adds no data to `SymbolTable`, `ModuleEntry`, `Scheme`, or any cached type. It is the same category of addition as `ModuleAliases` itself (a bare alias over a `DashMap`). Per the no-`cranelisp-types`-*change* constraint as the user means it (no change to the *interface data model* — no marker on entries, no field on tables), **this satisfies "cranelisp-types-free."** A bare type alias beside an existing identical alias is configuration plumbing, not a model change.

> **The honest fork, surfaced for the resolving fire.** Two realizations, both cranelisp-types-data-model-free:
> - **(a) Type alias in `cranelisp-types`** (recommended) — `PreludeFallback` alias beside `ModuleAliases`; `check_forms` gains a 5th parameter `prelude_fallback: &PreludeFallback`. Clean naming, mirrors `module_aliases` exactly. Adds one alias line to a `cranelisp-types` file → **needs an `/arch` nod** (the file is `/arch`-owned) but is NOT a data-model change.
> - **(b) Define the alias int-side** (`src/`), pass `&DashMap<ModuleFullPath, bool>` directly as the 5th `check_forms` param using the bare `dashmap` type. Zero `cranelisp-types` edit. Slightly less self-documenting at the typecheck boundary, but fully `/arch`-untouched.
>
> **Recommendation: (a).** It mirrors the `ModuleAliases` precedent exactly and reads correctly at the typecheck boundary. The `/arch` nod is for a single type-alias line, not a model change. If `/arch` declines even the alias, fall to (b) with no loss of behavior. **Either way, `check_forms` gains one parameter** (§2.7.4) — that IS an int↔typecheck boundary change the two `/dev` agents must land in lockstep.

### 2.7.3 The exact `check_forms` signature change (int↔typecheck boundary)

The bit must reach typecheck's resolution, and `check_forms` is the single entry. Today:

```rust
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
) -> Result<(), CheckError>
```

Target — **one added parameter**, threaded onto `TypeCheckEnv` exactly as `module_aliases` is:

```rust
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,   // NEW — session-side, read-only
) -> Result<(), CheckError>
```

- `TypeCheckEnv` gains `pub(crate) prelude_fallback: &'a PreludeFallback` beside `module_aliases` (`checker.rs:204`); `new` / `new_with_staging` gain the matching parameter (`checker.rs:345,375`).
- **All int call sites** thread `&self.shared.prelude_fallback` (the new SharedState field) at the same points they thread `&self.shared.module_aliases`: `src/worker.rs:288`, `src/cluster.rs:216`, `src/session_v4.rs:2301/3228/3268/4464`, and the `ModuleCompiler`/`WorkerCtx` carriers (`worker.rs:412,483`) gain a parallel `prelude_fallback: &'a PreludeFallback` field.
- **Test call sites** in `form.rs` / `platform.rs` pass `&PreludeFallback::default()` (empty ⇒ all-OFF, matching today's no-prelude unit-test envs).

**This is a known, bounded boundary change** — additive (one read-only parameter), mechanical at every call site, and symmetric with the existing `module_aliases` thread. It needs the two `/dev` agents to agree on the parameter name/position (pinned here) and lands in one cross-crate change-set. **Flag: needs an `/arch` nod** for the `PreludeFallback` alias under realization (a) — see §2.7.2.

### 2.7.4 The installer populates the bit — `inject_prelude_if_needed` (`src/worker.rs:3055`)

`inject_prelude_if_needed` already computes the exact ON condition (it early-returns OFF for `*module == "prelude"` and when `sexps_reference_prelude(sexps)` is true; `worker.rs:3061,3067`). The change:

- **On the ON path** (module did not reference prelude, prelude is loaded/loadable): instead of the two `install_imports([prelude_spec])` flatten calls (`worker.rs:3085`, `:3125`), **`ctx.prelude_fallback.insert(module.clone(), true)`**. Keep the discovery / `register_dep` / `register_module` / `block_for_typecheck` drive verbatim — prelude must still be loaded for the fallback to consult its table.
- **On the OFF paths** (early returns): do nothing — absence-is-OFF (§2.7.1). No insert needed.

`ModuleCompiler` (`worker.rs:412`) gains `prelude_fallback: &'a PreludeFallback` so `inject_prelude_if_needed` can write it; int threads `&self.shared.prelude_fallback` where it builds the `ModuleCompiler` (the same place it threads `module_aliases`).

### 2.7.5 The resolution-fallback algorithm — the two chokepoints

**Chokepoint 1 — `probe_module_entry_owned` (`checker.rs:979`), the chain-follow family.** This is the single entry for `lookup_in_current_module` → `lookup` (value/scheme) AND `resolve_terminal_entry_and_home` → `resolve_entry_in_current_module` (entries: constructors, trait decls, type defs). The fallback fires **only for the bare-name, current-module probe** — i.e. when the *caller* is probing `state.current_module` and missed. The cleanest pin keeps `probe_module_entry_owned` itself a pure single-module primitive (it is also called for *explicitly named* modules via `resolve_fq_symbol`, which must NOT fall back) and adds the fallback at the **current-module callers**:

```text
fn probe_current_or_prelude(env, state, name) -> Option<ModuleEntry>:
    if let Some(e) = env.probe_module_entry_owned(&state.current_module, name):
        return Some(e)
    // inner miss — consult the outer scope iff the bit is ON for this module
    if env.prelude_fallback.get(&state.current_module).map(|b| *b).unwrap_or(false):
        // chain-follow from prelude's OWN table; primitives reach here via
        // prelude's (export [primitives [*]]) Import edges (Decision 0048)
        return env.probe_module_entry_owned(&ModuleFullPath::from("prelude"), name)
    None
```

- `lookup_in_current_module` (`checker.rs:957–969`) and `resolve_entry_in_current_module` (`checker.rs:1081`) call `probe_current_or_prelude` instead of probing `current_module` directly. Both already chain-follow downstream (the existing `extract_scheme_from_entry_owned` / `resolve_terminal_entry_and_home` machinery), so the prelude `Import`→primitives edge is followed for free — **primitives-via-prelude survives via the re-export chain-follow through the FALLBACK, not a name-key** (the §2 green-guard constraint).
- **Explicit `fq.module`-qualified probes do NOT fall back:** `resolve_fq_symbol` (`checker.rs:1071`) and `resolve_terminal_entry_and_home(explicit_module, …)` keep calling the bare `probe_module_entry_owned` on the *named* module. The fallback is wired only at the two *current-module* entry points. (The `lookup` qualified branch at `checker.rs:914–951` is unaffected — it names modules directly.)

**Chokepoint 2 — the `current_symbol_table`→`View` (`checker.rs:416`) feeding the 6 `cranelisp_types::resolve` callers.** The bare-name `resolve` callers (`resolve_type`, `resolve_trait`, the `resolve_constructor` family, `resolve_type_expr_in_module`) build their `first_hop` from `current_symbol_table(state)`. Phase 3 weighed two realizations: a **two-hop view** (make `current_symbol_table` present `union(current, prelude)` so `first_hop.lookup` transparently falls back) versus **caller-side retry** (each bare-name caller re-runs `resolve` rooted at prelude on a not-found miss). The two-hop view was originally **preferred** as the one-chokepoint option.

> **AS BUILT (S78 Wave 4) — caller-side retry CHOSEN; two-hop view REJECTED.** The implementation realized the fallback as a **caller-side retry** (`resolve_current_or_prelude`, `checker.rs:824`), NOT a two-hop view. The two-hop view was rejected because the shared `View` newtype carries **at most two sources** (staging + live) — `SymbolTableRead::Cluster { staging, live }` is exactly `View::union(staging, live)`; `Live` is `View::single(live)`. Adding prelude as a **third** source would require a `cranelisp-types` view-type change (a wider `View` arity), which §2.7.7 commits to NOT making (cranelisp-types-free). So the prelude hop is realized caller-side instead: `resolve_current_or_prelude` runs the normal first-hop `resolve`, and on a not-found-class error (`TypeNotFound`/`TraitNotFound`/`ConstructorNotFound`) retries `resolve` rooted at the `prelude` module with a **`View::single(prelude_live)`** view over prelude's own table. The retried resolve chain-follows prelude's `(export [primitives [*]])` re-export edges to the canonical entry, so primitives-via-prelude resolve through the fallback (not a name-key). `PrivateInaccessible` and `QualifiedModuleUnknown` are NOT retried. The realization is **sound and self-documented** in the `resolve_current_or_prelude` rustdoc (`checker.rs:788–823`), which carries the full rationale (the `View`-arity limit and the "No change to `cranelisp_types::resolve` itself" §2.7.5 constraint it honours). The six bare-name callers route through `resolve_current_or_prelude` (`checker.rs:920/955/983/1017/…`); `resolve_macro_head` (`resolve.rs:357`, via int's `recognize_macro_head`) flows through the same resolve with no separate change.

**How this fixes the 3 import-shadow REDs (§/qa).** Under flattening, an explicit `(import [m [foo]])` of a prelude-provided `foo` produced TWO `Import` entries in M's inner table (the flattened prelude `foo` + the explicit `foo`) → `insert_detecting_ambiguity` fired `Ambiguous` → bare `foo` poisoned → "undefined variable". Under the outer-scope model, **prelude `foo` is no longer in M's inner table at all** (flattening removed, §2.7.4). M's table holds the explicit import as the *sole* `foo` entry → no ambiguity, it wins, exit-1005-clean. The fallback never enters (inner hit). **Fix is structural, not a skip.**

**How this preserves the 12 greens.** Local-def shadow (inner hit before fallback); explicit-vs-explicit ambiguity ×2 (both in inner table, fallback never consulted); prelude refusal `(import [prelude []])` / selective (bit OFF → no fallback, exactly as the OFF gate today); primitives-via-prelude ×3 (the fallback hop chain-follows prelude's `(export [primitives [*]])` → canonical primitive entry, §2.7.5 chokepoint-1 bullet). The qualified-still-works greens are untouched (qualified never used flattening).

**AS BUILT (S78 Wave 4) — the prelude retry is PUBLIC-ONLY (`/review` I-1) + the fallback guard is extracted.** Two implementation realities the Phase-3 pin did not state, now recorded:

1. **Public-only outer scope.** The implicit prelude outer scope exposes only **PUBLIC** prelude bindings as bare names — private prelude symbols are NOT bare-reachable from a user module. The `cranelisp-types` visibility rule is `entry.is_public() || in_subtree(current_module, home)`, and a user module is never in prelude's subtree, so reachability reduces to `entry.is_public()`. But the retry is *rooted at* `prelude` (so the chain-follow and terminal `home` are correct), which would make `cranelisp_types::resolve` evaluate visibility with `from_module = prelude` (and `in_subtree(prelude, prelude)` is true) — a Private prelude entry would then resolve. That is the I-1 leak. The fix is a **post-filter on visibility relative to the ORIGINAL user `current_module`**: every prelude-hop terminal is checked with `prelude_terminal_visible` (= `entry.is_public()`), and a private hit is treated as **not-found** (it does NOT resolve and does NOT shadow). Trait-method `Def` entries inherit the declared visibility of their trait, so a method of a private prelude trait is correctly unreachable as a bare name (`find_hkt_param_index_in_module`'s `public_only = true` arm, `traits.rs:2047`). Documented in the `prelude_terminal_visible` + `resolve_current_or_prelude` rustdoc (`checker.rs:771–823`).

2. **Extracted fallback guard.** The bit + self-fallback guard (`current_module != "prelude" && bit ON`) was copy-pasted across the bare-name chokepoints; it is extracted into one helper `prelude_fallback_target(current_module) -> Option<ModuleFullPath>` (`checker.rs:758`) that returns `Some(prelude_path)` iff the [`PreludeFallback`] bit is ON **and** the module is not prelude itself (a module never falls back onto itself; absence-is-OFF). Every chokepoint — `resolve_current_or_prelude`, `probe_current_or_prelude`, `resolve_entry_in_current_module`, the `resolve_type_expr_in_module` leaf resolver, and `find_hkt_param_index_in_registry` — routes its ON/OFF decision through this single helper, so the guard is one source of truth.

### 2.7.6 Introspection reads the bit too (`describe_symbol` + `handle_imports`)

`describe_symbol` (`session_v4.rs:1451`) and `handle_imports` (`session_v4.rs:2898`) run **session-side** (not through `check_forms`), so they read `self.shared.prelude_fallback` directly (the SharedState field) — no threading needed, they already hold `&self.shared`. Detailed in §2.6 (presentation) and §2.7.8 (split).

### 2.7.7 cranelisp-types-free confirmation (summary)

| Surface | Change | cranelisp-types data-model touched? |
|---|---|---|
| Fallback bit storage | `DashMap<ModuleFullPath, bool>` on `SharedState` (`src/`) | No — session-side, unserialized |
| Type name | `PreludeFallback` type **alias** beside `ModuleAliases` (realization (a)) | **Alias only** — no struct/enum/field; `/arch` nod for the alias line |
| `check_forms` | +1 read-only param `prelude_fallback` | No — signature, not data model |
| `TypeCheckEnv` | +1 borrowed field `&'a PreludeFallback` | No — typecheck-internal |
| Resolution | fallback at the 2 current-module chokepoints | No — at callers/view, NOT inside `cranelisp_types::resolve` |

**No `ModuleEntry`/`Scheme`/`SymbolTable`/cache-schema change.** The only `cranelisp-types` *file* touch is the one-line `PreludeFallback` alias under realization (a) — surfaced for the `/arch` nod, NOT a data-model change. Under (b) even that is zero.

### 2.7.8 The `/dev (cranelisp-typecheck)` vs `/dev (src/)` split + shared interface + landing order

**Shared interface (the contract both agents implement against):**
- `check_forms` gains 5th param `prelude_fallback: &PreludeFallback` (§2.7.3).
- `PreludeFallback = DashMap<ModuleFullPath, bool>`; `true`/present ⇒ ON, absent/`false` ⇒ OFF.
- Semantics: int inserts `(module, true)` exactly when `inject_prelude_if_needed` takes its ON path; typecheck falls back to the `prelude` module's table on a bare-name current-module miss iff the bit is ON.

**`/dev (cranelisp-typecheck)` does:**
1. Add `prelude_fallback: &'a PreludeFallback` to `TypeCheckEnv` + `new`/`new_with_staging` + the `check_forms` 5th param (§2.7.3).
2. **Chokepoint 1:** add `probe_current_or_prelude` and route `lookup_in_current_module` + `resolve_entry_in_current_module` through it; leave `resolve_fq_symbol` / explicit-module probes on the bare primitive (§2.7.5).
3. **Chokepoint 2:** route the 6 `cranelisp_types::resolve` bare-name callers through a caller-side retry (`resolve_current_or_prelude`) that re-runs `resolve` rooted at prelude with a `View::single(prelude_live)` view on a not-found miss, bit-gated via `prelude_fallback_target`, public-only post-filter per I-1 (§2.7.5 AS BUILT — the two-hop view was rejected on the `View` two-source arity limit).
4. Unit tests inside the crate: bare-name-via-prelude-fallback hit/miss, bit-OFF no-fallback, explicit-import-wins-no-ambiguity, qualified-no-fallback (per `feedback_unit_tests_with_dev`).

**`/dev (src/)` does:**
1. Add `pub prelude_fallback: PreludeFallback` to `SharedState` (`session_v4.rs:750` neighbourhood); init `::default()` everywhere `module_aliases` is init (`session_v4.rs:1111`, `scheduler.rs:1796`).
2. Add `PreludeFallback` alias (realization (a), `cranelisp-types`, `/arch` nod) OR int-side (realization (b)).
3. Thread `&self.shared.prelude_fallback` at every `check_forms`/`ModuleCompiler`/`WorkerCtx` site that threads `module_aliases` (§2.7.3); add the `prelude_fallback` field to `ModuleCompiler` (`worker.rs:412`) + `WorkerCtx` (`worker.rs:483`).
4. **Installer:** `inject_prelude_if_needed` replaces the two `install_imports([prelude_spec])` with `ctx.prelude_fallback.insert(module.clone(), true)`, keeping the load drive (§2.7.4).
5. **Delete `is_seeded`** (`imports.rs:311–317`) + fix the doc comment (`imports.rs:273–276`); `insert_detecting_ambiguity` reverts to uniform `Ambiguous` (§2.3 item 3).
6. **Introspection:** `handle_imports` `Prelude (implicit)` group + `describe_symbol` prelude hop, both gated on `self.shared.prelude_fallback` (§2.6, §2.7.6).

**Landing order — `/dev (src/)` field + alias first, then lockstep on the signature.** The `check_forms` 5th-param change breaks the build the moment either side lands alone. Sequence:
1. **`/dev (src/)`** lands the `SharedState.prelude_fallback` field + the `PreludeFallback` alias (the *type* the signature will name) — build stays green (no caller passes it yet).
2. **Lockstep signature flip:** `/dev (cranelisp-typecheck)` adds the `check_forms`/`TypeCheckEnv` param AND `/dev (src/)` threads `&self.shared.prelude_fallback` at every call site **in the same change-set** (the build is red between these two edits — expected; `feedback_facade_first_migration` / additive-boundary discipline). The two `/dev` agents coordinate this one commit.
3. **`/dev (cranelisp-typecheck)`** lands the two chokepoint algorithms (now the bit is readable end-to-end); the import-shadow REDs go green.
4. **`/dev (src/)`** lands the installer `is_seeded` deletion + introspection adds; the remaining REDs go green, the 12 greens hold.

The typecheck chokepoints (step 3) and the installer deletion (step 4) are **independent once the bit is threaded** (step 2) — they can land in either order or in parallel, but both must be present for the full §2 test set to pass (chokepoints make primitives-via-prelude resolve through the fallback; installer deletion stops the flattening that poisons import-shadow). **Neither alone is shippable** — landing the installer deletion without the chokepoints would break primitives-via-prelude (the flattened entry that was resolving them is gone with no fallback to replace it). The two `/dev` agents land within one wave; `/qa` gates on the full 18-test set (12 green-hold + 6 red-fix) green.

---

## 3. Single-orchestration for the entry module (B1)

### 3.1 The defect (restated structurally)

The entry/REPL module is **dual-orchestrated**:

- **Eval-thread path:** `process_single_form` (`session_v4.rs:2257`) drives `worker::process_cluster_once` directly on the eval thread for each REPL form, against the entry module's live table.
- **Pool path:** the same module is registered with `scheduler.register_module(module, sexps, false)` (`session_v4.rs:1975`) → `ModuleState { sexps: Some(...) }`, enqueued into `typecheck_next`, **pool-claimable**. On a dep gap, `block_for_typecheck(entry, dep)` → `try_unblock_locked(entry)` (`scheduler.rs:1382`) **unconditionally requeues** `entry` onto `typecheck_first/next` → a pool worker runs `process_cluster(entry, sexps_from_ModuleState)` **concurrently with the eval thread's retry of the same module's live table.**

Two actors mutating one module's staging→live cycle = the in-progress-sharing class the S78 restructure removed from `module_sexps`, now relocated to `ModuleState.sexps`. `/review` rated it Blocker B1. It is benign-by-luck only when the entry source is empty (`String::new()` fresh REPL → worker re-typechecks empty = no-op); it is **not benign** for a non-empty entry (`--run`-then-REPL, or any non-empty entry module that hits an import gap).

### 3.2 The false invariant comment

`scheduler.rs:89–97` (the `ModuleState.sexps` field doc) asserts the eval/REPL caller module is "**never requeued onto the pool for a fresh typecheck of its own sexps**" and uses `sexps: None` for it. This is **false as built**: `register_module_with_source` registers the entry/REPL module with `sexps: Some(...)` (§3.1), so `try_unblock_locked` *does* requeue it. The comment documents the *intended* invariant; the code violates it. **This false comment must not ship regardless of the fix chosen.**

### 3.3 The fix — single-orchestrator ownership (NOT a name-keyed skip)

The fix must be **structural**, not a `"user"`/`entry`-keyed skip in `block_for_typecheck`/`try_unblock_locked` (that would be the same name-special-casing disease in a new place). Two structural options:

- **(3a) Eval submits + waits like any module** (§6.2 BC handoff pattern). The eval thread stops driving `process_cluster_once` directly. It submits the REPL form's cluster to the scheduler (registers the entry module's sexps as a normal work packet) and **waits on the terminal signal** (`wait_inmem_complete_blocking`), exactly as `--run` does. A single pool worker is the sole orchestrator of every module including the entry. This is the *uniform* shape — REPL and batch converge on "register + wait." It is the larger change (the eval thread's bespoke `process_single_form` retry loop + REPL `check_state` threading dissolves into the worker path), and it must preserve REPL semantics (per-form display info, `repl_check_state` continuity, additive `ModuleStrategy`).

- **(3b) The entry/REPL module is never given a pool-claimable `ModuleState`.** The eval thread remains the sole orchestrator of the entry module; the module is registered with `sexps: None` (making the false invariant *true*), so `try_unblock_locked` has nothing to requeue (or the entry module is not registered into the pool queues at all — it lives only as a live symbol table the eval thread drives). Dep gaps the eval thread hits are driven by the eval thread's own wait (`wait_module_inmem_complete_blocking(dep)` — the §3 eval-path wrapper already does this). The pool orchestrates *dependencies*; the eval thread orchestrates *the entry module*. Single owner per module, structurally.

**Design recommendation: (3b), with (3a) as the principled end-state.** (3b) is the minimal, structurally-sound fix that makes the false invariant true and removes the dual actor: register the eval-owned module with `sexps: None` and ensure `try_unblock_locked` (which already early-returns when `pool != TypecheckBlocked`) never requeues an eval-owned module for its *own* typecheck. The justification is **ownership**, not name: the eval thread *owns* this module's orchestration, so the scheduler must not hand it a pool-claimable typecheck packet for the same sexps. This is decided by the registration shape (`sexps: None` / not-pool-enqueued), a per-module *role* property the session sets, NOT by matching the literal `"user"`.

(3a) is the cleaner long-term convergence (one orchestration path for all modules, §6.2's "submit + wait"), but it is a larger eval-path rewrite and risks REPL display/`check_state` regressions; recommend sequencing it as S79 if the minimal (3b) lands first. **Either way the fix is keyed on orchestration ownership, not module name** — which is the no-special-casing principle satisfied.

### 3.4 Reconciliation with `s78-implementation.md §3` (3a)

`s78-implementation.md §3` resolved the eval path as **(3a) — `process_cluster` worker-only; eval keeps its own loop** calling `process_cluster_once` + `wait_module_inmem_complete_blocking` + retry. That decision is about the *gap-drive shape* (eval owns its wait loop; worker owns the requeue loop) and is **consistent with this doc's (3b)**: in `s78-implementation.md`'s sense, the eval thread already owns its own loop and waits on deps itself. The residual B1 defect is that the entry module is *also* registered with `sexps: Some` and pool-claimable — i.e. the eval-owned module leaked a worker-path packet. (3b) closes that leak by registering the eval-owned module with `sexps: None` / not pool-enqueued. The two docs do not conflict: `s78-implementation.md §3` pins the *eval gap-wait wrapper*; this §3 pins the *entry-module orchestration ownership* so no second actor exists. /dev reconciles both into the eval path in one pass.

---

## 4. Expunge list — docs/comments asserting `user`/`primitives` special-casing

For the /dev (code comments) + /docs (design text) pass. **Audit-first: surfaced for sign-off, NOT yet expunged.** Each is `file:anchor — what's wrong`.

### Code comments (/dev, in the same change-set as the §1–§3 fixes)

- `session_v4.rs:1007` — "Seed the 'user' module before register_builtins (which registers special forms on it)." **Stale + wrong**: special forms mount at root `""`; `register_builtins` is gone (→ `mount_synthetic_modules`). Delete with the pre-seed (§1.3).
- `session_v4.rs:1055–1056` — "`primitives` and `user` are already mounted above; this only adds to them." **Stale**: `mount_synthetic_modules` does not touch `user`. Correct to name only the modules it touches (`primitives`/`macros`/root).
- `session_v4.rs:1026–1027` — "`register_builtins` (next call) short-circuits the primitives-module creation." **Stale**: `register_builtins` is `mount_synthetic_modules`. Correct the name.
- `imports.rs:273–276` — `insert_detecting_ambiguity` doc: "seeded builtins (`user`/`primitives`) take priority." **Wrong basis**: prelude is an outer scope (§2), not a flattened tier; rewrite to describe uniform §8.6.4 ambiguity over the inner table only — no `user`/`primitives` mention, no precedence-tier language.
- `imports.rs:311–317` — the `is_seeded` closure + its inline rationale. Delete (§2.3).
- `scheduler.rs:89–97` — `ModuleState.sexps` field doc, "never requeued onto the pool for a fresh typecheck of its own sexps." **False invariant** (§3.2). Rewrite to state the *enforced* invariant after the §3 fix (eval-owned module registered `sexps: None` / not pool-enqueued, so genuinely never requeued).
- `session_v4.rs:2680–2682` — `handle_mod` `"user"` default (comment "switch module namespace"): correct to "entry module" semantics (§1.4).

### Design text (/docs + /arch, file FIXMEs or own-skill edits)

- `bounded-contexts.md §6` (int) — verify no statement privileges `user`/`primitives` as special modules; the int BC should state the entry module is ordinary + the prelude-as-outer-scope import model (inner table = explicit imports + defs; prelude fallback on a miss). (Currently §6 was beyond the loaded page; /arch confirms at action time. The §6.2 "submit + wait" handoff is the (3a) end-state reference.)
- `facades/int.md` — grep for `"user"` / `current_repl_module` / `is_seeded` / "seeded builtins"; reconcile any text asserting `user`-as-special or the seeded-import skip. (int is the last live facade — /arch-owned; action in the resolving pass.)
- `src/CLAUDE.md §"Synthetic-module mount + import installer"` — the `install_imports`/`insert_detecting_ambiguity` paragraph should describe the **prelude-as-outer-scope fallback** (inner table = explicit imports + local defs; prelude consulted on a miss, gated per-module) + reference §8.6.4/§8.8, not the `is_seeded` skip (the paragraph predates the fix). Also note `inject_prelude_if_needed` now sets the fallback bit rather than flattening. /dev-owned.
- `design/int/imports.rs`-adjacent design docs (`private-submodule-import.md`, any S76 W2 record) — grep for the `is_seeded` rationale; supersede.
- `s78-implementation.md` + `s77-int-restructure.md` — note the B1 residual is resolved by this doc's §3 (cross-reference; no contradiction).

> **/arch action discipline.** The `bounded-contexts.md` / `facades/int.md` edits are /arch-owned canonical-set edits and land at the *resolving* fire (after user sign-off), per `feedback_review_before_enact` — NOT in this audit pass. This doc names them; it does not enact them.

---

## 5. Disposition, sizing, Principle recommendation

### 5.1 Disposition — S78-fold vs S79

**Recommendation: split.**

- **§3 (single-orchestration B1) + §3.2 false-comment + the §4 `scheduler.rs:89–97` comment → S78-fold (minimal (3b)).** B1 is a `/review` Blocker on the restructure this sprint delivered; it is the restructure's own residual (the in-progress-sharing class relocated to `ModuleState.sexps`). The minimal (3b) fix — register the eval-owned module `sexps: None` / not pool-enqueued + fix the false comment — is small, self-contained, and closes the Blocker. Folding it into S78 keeps the restructure's soundness claim honest (the substrate is genuinely gone, not just for the worker path). Gate: the existing heisenbug stress suite (`heisenbug_race_reduced_concurrent_import_pairs`, `cache_repl_loads_heisenbug_parallel_stress`) + a new `--run`-then-REPL-then-import-gap repro (/qa).

- **§1 (pre-seed deletion + 3 hardcoded-`"user"` defaults) + §2 (prelude-as-outer-scope, delete `is_seeded`) → S79.** These are correctness improvements for **non-`user` entry programs** (a latent-bug class) and a faithful re-shape of prelude resolution — not active Blockers on the S78 restructure. The blast-radius walk (§2.5) **revises the prior sizing**: §2 is now confirmed **`cranelisp-typecheck` + `src/`, with NO `cranelisp-types` change** (the marker is rejected) and NO /spec *model* decision (the model is settled; only editorial §8.6.4/§8.8 alignment remains). But it is no longer a trivial installer-only delete: the outer-scope fallback touches **two typecheck resolution chokepoints** (`probe_module_entry_owned` + the `current_symbol_table`→`View` feeding `cranelisp_types::resolve`) plus two int introspection adds. That is a coherent **typecheck + int** D/D/R cycle (`/design`(typecheck)+`/design`(int) → `/dev`(typecheck)+`/dev`(src) → `/qa`), warranting its own wave, not a fold into the restructure-close. §1's pre-seed deletion is low-risk but couples to §1.4's entry-name threading; bundle with §2 for one coherent "entry-module-is-ordinary + prelude-is-an-outer-scope" S79 wave.

> **Rationale for not folding §1+§2 into S78.** S78 is the single-deliverable restructure sprint (user-directed: "we don't want substantial change to persist"). §1+§2 are a *separate* concern (entry-module identity + prelude scope-layering). §2 in particular spans **two crates** (`cranelisp-typecheck` resolution + `src/` installer/introspection) and changes the bare-name resolution path — material enough to deserve its own dispatch and `/qa` coverage (shadowing, refusal, selective-import, primitives-via-prelude). Folding it risks scope-creeping the restructure close. The Blocker (§3) is the only part that is genuinely S78's residual. **What S78 fold-vs-defer turns on is unchanged by the blast-radius finding** — §2 was already deferred; the walk confirms the deferral is correct and re-scopes the S79 work crate-accurately (typecheck-inclusive, cranelisp-types-free).

### 5.2 Sizing

| Item | Skill(s) | Effort | Gating |
|---|---|---|---|
| §3 minimal (3b) + false comment | /design(int)→/dev(src/)→/qa(repro)→/review | S | S78-fold; gated on heisenbug stress + new `--run`-then-REPL-gap repro green |
| §1 pre-seed delete + 3 entry-name defaults | /design(int)→/dev(src/) | S–M | S79; couples §1.4 entry-name threading |
| §2 prelude-as-outer-scope + `is_seeded` delete | /design(typecheck)+/design(int) → /dev(typecheck: 2 resolution chokepoints)+/dev(src: installer+2 introspection adds) → /qa | M | S79; **NO `cranelisp-types` change, NO marker, NO /spec model decision** — only editorial /spec §8.6.4/§8.8 alignment (non-gating). Crates: `cranelisp-typecheck` + `src/` |
| §4 doc/comment expunge | /dev (code) + /docs + /arch (canonical set) | S | Lands with its owning fix (cascade discipline) |
| §3 (3a) full uniform submit+wait | /design(int)→/dev→/qa | L | S79+ (optional convergence; only if (3b) proves insufficient) |

### 5.3 Principle recommendation — PROPOSED, for sign-off (do NOT author without surfacing)

The "no module special-casing except synthetic + prelude" rule is currently **implicit** — it lives in spec §8.8.1/§5.9 (the implied-import set) and in this sprint's lived experience, but it is not an architectural Principle. The four manifestations above show the implementation repeatedly violated it because nothing in the Principle register named it. A Principle would give `/review` and `/design` an explicit criterion to flag the next `"user"`/`is_seeded`-shaped accretion.

**Proposed Principle 19 (wording for sign-off — not yet authored):**

> **No module is privileged by name.** The compiler treats every module uniformly. The only modules with compiler-special status are the *synthetic* modules (`primitives`, `platforms`, `macros`, root special-forms `""`), which are compiler-seeded, and `prelude`, the single implied import every user module receives (spec §8.8.1). The **entry module** — the `main`-bearing or REPL-target module — is an ordinary module; `"user"` is only its default name, not a privileged identity. No code path may key behaviour on a module's *name* (`m == "user"`, etc.); behaviour keys on a module's *role* (synthetic vs user; inner-scope table vs the prelude outer-scope fallback; eval-owned vs pool-orchestrated) carried as data, never on a string literal. Enforce structurally where possible (Principle 18): a name-keyed module check is a defect smell.

**Per `feedback_explicit_decision_review` + `feedback_manifestation_site_question`:** this Principle is **proposed, not authored.** /arch authors `principles/19-*.md` + the index entry only at **sprint close (Phase 7)** with user sign-off, citing this sprint as the motivating context. Surfacing it now; the user reviews substance + rationale before it binds. Its manifestation site is the Principle register (cross-cutting axiom); the four manifestations + the prelude-as-outer-scope model are its grounding.

---

## 6. Open items requiring sign-off

1. **/spec §8.6.4/§8.8 editorial alignment (NON-gating)** — the prelude-as-outer-scope model is **settled** (user, 2026-06-11) and grounded in the existing §8.6.4 `let`-analogy text; it needs no new model ruling. The minimal wording change makes the outer-scope framing *normative* rather than describing prelude as flattened-with-a-shadow-exception. **Specify (do not enact):** in §8.6.4, state that the implicit prelude is an **outer scope consulted on a resolution miss in the module's own (inner) scope**, not a set of bindings materialised into the module table; the existing "shadow just as inner `let` shadows outer" line then reads literally. In §8.8 (implicit-prelude injection / §8.8.1 "module does not reference prelude"), state that "injection" means **activating the prelude outer-scope fallback** for the module (ON unless the module refuses/references prelude), not copying prelude's bindings in. This is editorial; §2's implementation does **not** gate on it. File `target: /spec` FIXME at the resolving fire.
2. **§3 fix choice — (3b) minimal vs (3a) uniform** — recommended (3b) for S78-fold, (3a) deferred. **User picks** whether the Blocker fix is the minimal ownership-marker (3b) or the full submit+wait convergence (3a).
3. **Disposition split (§5.1)** — S78-fold §3 / S79 §1+§2. **User confirms** the split (or folds all into S78). The blast-radius walk (§2.5) confirms §2 is `cranelisp-typecheck`+`src/` with **no cross-crate (`cranelisp-types`) dependency and no /spec model gate** — so the only reason to keep §2 in S79 is scope hygiene of the restructure close, not an external blocker.
4. **Where the per-module fallback bit lives** — **RESOLVED (§2.7, Wave-4 design):** session-side companion `DashMap<ModuleFullPath, bool>` on `SharedState`, exactly parallel to `module_aliases`, threaded into typecheck as a new 5th read-only `check_forms` parameter `prelude_fallback: &PreludeFallback` and carried on `TypeCheckEnv`. The `SymbolTable`-field option is **rejected** (it would be a `cranelisp-types` data-model/cache-schema change). The session-side home keeps the bit unserialized and recomputed-per-session. **The one residual `/arch` touch** is a single `PreludeFallback` type-*alias* line beside `ModuleAliases` (`cranelisp-types/src/module.rs:419`) under realization (a) — an alias, NOT a data-model change; realization (b) defines it int-side for zero `cranelisp-types` touch. The `check_forms` +1-param signature change is an int↔typecheck boundary the two `/dev` agents land in lockstep (§2.7.3, §2.7.8). **/arch nod needed only for the alias line.**
5. **Principle 19 (§5.3)** — proposed; authored at Phase-7 close on sign-off.

---

## Change history

- 2026-06-10 (`/arch`, Phase-5 PIVOT audit-first pass): authored. Source-verified the four hardcoded-`"user"` manifestations + the dual-orchestration B1 against the working tree (`main.rs:172`, `session_v4.rs:1005/1154/2682/3626/4559/1953/2257`, `imports.rs:277/311`, `bootstrap.rs:295`, `scheduler.rs:89/334/1382`). Verdict: ctor pre-seed vestigial/deletable (special forms at root `""`, `register_builtins`→`mount_synthetic_modules` touches no `user`); two-tier import model recommended via a `cranelisp-types` implied-provenance marker (2.3a); single-orchestration via ownership-marker `sexps: None` (3b minimal, S78-fold) with submit+wait (3a) as S79 convergence; disposition split §3→S78 / §1+§2→S79; Principle 19 proposed for Phase-7 authoring. Audit-first: doc + surfaced sign-off items only; no canonical-set edits, no code/test changes enacted.
- 2026-06-11 (`/design` (int), Wave-4 realization pin): authored **§2.7 REALIZATION** pinning the load-bearing unknown (§6 open-item 4) — fallback-bit home + cross-crate threading + resolution algorithm + `/dev` split. Source-confirmed: `ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>` (`module.rs:419`) on `SharedState` (`session_v4.rs:750`), threaded as `check_forms`'s 4th param (`form.rs:83`) onto `TypeCheckEnv` (`checker.rs:204`). **Pinned:** companion `PreludeFallback = DashMap<ModuleFullPath, bool>` session-side on `SharedState`, +1 read-only `check_forms` param, parallel to `module_aliases` at every call site — **no `cranelisp-types` data-model change** (only a one-line type-alias under realization (a), `/arch` nod; realization (b) is int-side, zero-touch). **Resolution algorithm:** `probe_current_or_prelude` wrapper at the 2 current-module chokepoints (`lookup_in_current_module`+`resolve_entry_in_current_module` via `probe_module_entry_owned`; `current_symbol_table`→`View` two-hop for the 6 `resolve` callers); explicit/`fq.module` probes do NOT fall back. Fixes the 3 import-shadow REDs structurally (prelude no longer in inner table → explicit import sole entry, no `Ambiguous`); preserves primitives-via-prelude via the fallback's chain-follow of prelude's `(export [primitives [*]])` (not a name-key). **§2.7.8 `/dev` split + landing order:** src/ lands field+alias first; lockstep `check_forms` signature flip; then typecheck chokepoints + src/ installer/`is_seeded`-delete/introspection, gated together on the 18-test set. §6 open-item-4 marked RESOLVED. Doc-only; no code/test changes; no canonical-set edits.
- 2026-06-11 (`/design` (int), Wave-5 as-built reconciliation): refreshed §2.7.5 Chokepoint 2 (+ the §2.5 blast-radius note + the §2.7.8 split step 3) to record the as-built realization. **Caller-side retry CHOSEN; two-hop view REJECTED** — the shared `View` newtype carries at most two sources (staging+live), so adding a third prelude source would need a `cranelisp-types` view-type change, which §2.7.7 commits NOT to make; the prelude hop is realized caller-side in `resolve_current_or_prelude` (`checker.rs:824`) as a `resolve` retry rooted at prelude over `View::single(prelude_live)`, sound + self-documented in the function rustdoc (`checker.rs:788–823`). Noted the **Wave-4 I-1 follow-on**: the prelude retry is **public-only** (private prelude symbols are not bare-reachable; the retry is post-filtered on `prelude_terminal_visible` = `entry.is_public()` relative to the original user module; trait-method `Def` entries inherit their trait's declared visibility, `traits.rs:2047` `public_only`), and the duplicated bit+self guard is extracted into `prelude_fallback_target` (`checker.rs:758`), the single source of truth routed by every bare-name chokepoint. Doc-only; no code/test changes; no canonical-set edits.
- 2026-06-11 (`/arch`, settled-model §2 reshape + blast-radius walk): §2 rewritten from the two-tier-flattened model to the **prelude-as-outer-scope fallback** model settled by the user (2026-06-11; `project_prelude_outer_scope`). Provenance-marker (2.3a) + install-order (2.3b) proposals **deleted/rejected**; `cranelisp-types` dependency **dropped**. Added §2.5 BLAST RADIUS (source-walked: typecheck `probe_module_entry_owned` `checker.rs:979` + `current_symbol_table`→`View` `checker.rs:416` feeding 6 `cranelisp_types::resolve` callers — **two chokepoints**; installer `inject_prelude_if_needed` `worker.rs:3055` + `is_seeded` delete `imports.rs:311`; introspection `handle_imports` `session_v4.rs:2898` + `describe_symbol` `session_v4.rs:1451`; `/list`+`/exports` unaffected; **backend FQSymbol/GOT-based — UNAFFECTED**, verified `jit.rs:110–157`). Added §2.6 `/imports` presentation decision (distinct `Prelude (implicit)` group). §5 sizing re-scoped: §2 is `cranelisp-typecheck`+`src/`, **NO `cranelisp-types` change, NO marker, NO /spec model gate** (only editorial §8.6.4/§8.8 alignment). §6 reframed: dropped the marker open-item; added the per-module-fallback-bit home question (session-side recommended to stay cranelisp-types-free). §1, §3, §4 carried unchanged. Audit-first: doc-only; no code/test changes; no canonical-set edits.
