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

2. **`cranelisp_types::resolve(... first_hop ...)`** — the shared resolver's unqualified branch (`resolve.rs:280–287`, `first_hop.lookup(name)`). Called from **six sites** in `checker.rs`: `:726` (`resolve_type`), `:768` (`resolve_trait`), `:803`/`:844` (`resolve_constructor` family), `:1155` (`resolve_qualified`'s composed form — qualified, no fallback needed), `:1711` (`resolve_type_expr_in_module`). The `first_hop` view is built by `current_symbol_table(state)` (`checker.rs:416–432`). **Single chokepoint, view-side:** make the bare-name first-hop a *two-hop* view (current module, then prelude when the bit is ON) so `first_hop.lookup` transparently falls back — OR have each of the ~5 bare-name callers retry `resolve` against prelude on `TypeNotFound`/`TraitNotFound`/`ConstructorNotFound`. The view-construction approach is the one-chokepoint option and is preferred; it touches `current_symbol_table` + the `View` it returns, both int-typecheck-local. **No change to `cranelisp_types::resolve` itself.**

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
4. **Where the per-module fallback bit lives** — recommended home is the per-module `SymbolTable` (a `prelude_fallback: bool`), readable by both int (which sets it in `inject_prelude_if_needed`) and typecheck (which consults it at the resolution chokepoints). `SymbolTable` is a `cranelisp-types` type, so a `bool` field there *would* be a `cranelisp-types` change — **alternative: hold the bit session-side** keyed by `ModuleFullPath` (int-owned `SharedState`), passed into typecheck via the existing `ModuleCompiler`/`check_forms` threading (the same channel `module_aliases` already uses read-only). **The session-side home keeps §2 cranelisp-types-free** and is recommended; /arch confirms at the resolving fire. (This is the one place the "no cranelisp-types change" claim has a fork — both forks are surfaced.)
5. **Principle 19 (§5.3)** — proposed; authored at Phase-7 close on sign-off.

---

## Change history

- 2026-06-10 (`/arch`, Phase-5 PIVOT audit-first pass): authored. Source-verified the four hardcoded-`"user"` manifestations + the dual-orchestration B1 against the working tree (`main.rs:172`, `session_v4.rs:1005/1154/2682/3626/4559/1953/2257`, `imports.rs:277/311`, `bootstrap.rs:295`, `scheduler.rs:89/334/1382`). Verdict: ctor pre-seed vestigial/deletable (special forms at root `""`, `register_builtins`→`mount_synthetic_modules` touches no `user`); two-tier import model recommended via a `cranelisp-types` implied-provenance marker (2.3a); single-orchestration via ownership-marker `sexps: None` (3b minimal, S78-fold) with submit+wait (3a) as S79 convergence; disposition split §3→S78 / §1+§2→S79; Principle 19 proposed for Phase-7 authoring. Audit-first: doc + surfaced sign-off items only; no canonical-set edits, no code/test changes enacted.
- 2026-06-11 (`/arch`, settled-model §2 reshape + blast-radius walk): §2 rewritten from the two-tier-flattened model to the **prelude-as-outer-scope fallback** model settled by the user (2026-06-11; `project_prelude_outer_scope`). Provenance-marker (2.3a) + install-order (2.3b) proposals **deleted/rejected**; `cranelisp-types` dependency **dropped**. Added §2.5 BLAST RADIUS (source-walked: typecheck `probe_module_entry_owned` `checker.rs:979` + `current_symbol_table`→`View` `checker.rs:416` feeding 6 `cranelisp_types::resolve` callers — **two chokepoints**; installer `inject_prelude_if_needed` `worker.rs:3055` + `is_seeded` delete `imports.rs:311`; introspection `handle_imports` `session_v4.rs:2898` + `describe_symbol` `session_v4.rs:1451`; `/list`+`/exports` unaffected; **backend FQSymbol/GOT-based — UNAFFECTED**, verified `jit.rs:110–157`). Added §2.6 `/imports` presentation decision (distinct `Prelude (implicit)` group). §5 sizing re-scoped: §2 is `cranelisp-typecheck`+`src/`, **NO `cranelisp-types` change, NO marker, NO /spec model gate** (only editorial §8.6.4/§8.8 alignment). §6 reframed: dropped the marker open-item; added the per-module-fallback-bit home question (session-side recommended to stay cranelisp-types-free). §1, §3, §4 carried unchanged. Audit-first: doc-only; no code/test changes; no canonical-set edits.
