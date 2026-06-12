---
number: 19
title: No module is privileged by name
---

# Principle 19 — No module is privileged by name

**Statement.** Resolution, orchestration, and visibility decisions key on a module's *role* — carried as **data** (a flag, a per-module bit, a structural relationship) — never on a name *literal* (`"user"`, `"primitives"`, `"main"`, …). The only modules with special status are:

- the **synthetic** modules `primitives`, `platforms`, and `macros` — special by *construction* (compiler-seeded; no source forms; `imports`/`exports` empty by invariant), not by a name match; and
- `prelude` — the one **implied import / outer scope**, special by its *declared role*, resolved via a per-module fallback bit (the prelude-fallback bit), not by a name check.

No other module is privileged. A name-literal comparison in a resolution / orchestration / visibility path (`if module == "user"`, `m == "user" || "primitives"`, a `"main"`-keyed branch) is an architectural defect under this Principle.

**The entry module is ordinary.** The *entry module* is the `main`-bearing module under `--run`/`--link`, or the REPL's current target. `"user"` is only the CLI's **default name** when no target is given (a fresh REPL, `cranelisp` with no file). Most programs have no `user` module — they have `sudoku`, `myapp`, whatever the target names. The entry module is ordinary in every respect: it receives the implicit prelude as an outer-scope fallback, it is subject to §8.6.4 ambiguity within its own (inner-scope) table, it has a normal symbol table, and it is orchestrated like any other module. Its only distinction is *role* — it holds `main` / is the REPL cursor — carried as data, never as a name literal. `/mod`, the REPL cursor (`current_repl_module`), init seeding, and the compile/cluster orchestrator all reference the entry-module *concept* (the name threaded in at session construction), never the literal `"user"`.

**Grounding (S78).** The de-special-casing sprint retracted accreted name-keying and replaced each instance with role-as-data:

- **`eval_owned` orchestration role-flag** — `ModuleState.eval_owned: bool` marks the entry module as eval-owned and therefore not pool-claimable. The orchestrator skips it *by role* (the flag), not by an `== "user"` match. This closes the dual-orchestration symptom (an eval thread and a compilation worker both claiming the entry module's gaps) at its disease — module privilege smeared across name literals.
- **`prelude_fallback` per-module bit** — the prelude is resolved as an **outer scope** consulted on a bare-name resolution miss, not flattened (materialised) into each module's table. The bit is ON for modules that receive the implicit prelude and OFF for modules that refuse or reference it (`(import [prelude []])` / selective import) — the same gate that governed implicit-prelude injection before. Primitives reach user code via prelude's `(export [primitives [*]])` re-export, chain-followed through the same fallback (Decision 0048 uniformity) — there is no per-module primitives seeding and no `"primitives"` name-key.
- **Retraction of `is_seeded`** — the `m == "user" || "primitives"` ambiguity-skip (an S76 hack papering over the flattened-prelude collision) deleted with the flattening. Explicit-vs-explicit ambiguity is unaffected; the bandage went away with the scar.
- **Entry name threaded at construction** — the entry-module name is a parameter of `CompilerSession::new`, not a literal recovered downstream. The vestigial `"user"` init-seed becomes `ensure_module_exists(entry_module)`; `current_repl_module`, the REPL check state, the test-runner state, `handle_mod("")`, and `run_test_by_name` all reference the threaded entry name.

**Enforcement.** Structurally where possible, per Principle 18 — role-as-data makes the wrong thing *unrepresentable* rather than relying on review to catch a name literal: an orchestrator that branches on `ModuleState.eval_owned` has no `"user"` string to mistype, and a resolver that consults a per-module bit cannot privilege a module it was never told to. Where the structural form is not yet complete, `/review` checks for name-literal special-casing in resolution / orchestration / visibility paths as a standing criterion: any new `if module == "<literal>"` in those paths is a finding, justified only when the literal names a synthetic module at its construction site (where the name is the module's *definition*, not a privilege test).

**Cross-references.**

- Principle 17 — Module locality in typecheck (the resolution-side companion: short-name resolution never probes `user` or any other module by name; the prelude fallback is a declared-role outer scope, not a name-keyed sweep).
- Principle 18 — Enforce architectural invariants structurally where possible (role-as-data is the structural mechanism this Principle prefers over a review-caught name literal).
- Concept origins: memory `project_entry_module_concept` (the entry-module concept; `"user"` is only the default CLI name) and `project_prelude_outer_scope` (prelude as an outer scope resolved by fallback, not flattened).
