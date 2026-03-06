# Sprint 7: Ring 2B — Cross-Module Wiring, REPL Chrome, Qualified Display

**Status**: COMPLETE
**Ring**: 2 (Abstraction) — fourth increment
**Goal**: Wire cross-module imports end-to-end, deliver REPL chrome (slash commands, banner, prompt, stderr), qualified display, primitives module, and pay down carried debt. Multi-sig + auto-curry deferred to Sprint 8 per /arch recommendation (scope risk).

## Scope

Sprint 6 delivered module infrastructure but cross-module calls are not end-to-end wired and the REPL lacks chrome. This sprint completes Ring 2B foundations and makes the REPL showcasable.

### Core deliverables

1. **Cross-module import resolution** — wire export registration in orchestrator, un-ignore 4 module tests (1x deferred from S6)
2. **REPL qualified display** — output `primitives/Int`, `user/id`, `Color.Red` notation, un-ignore 9 E2E tests (1x deferred from S6)
3. **Primitives module** — proper `primitives` synthetic module replacing current "user" module seeding hack

### REPL chrome (brought forward from Ring 4, progressive delivery)

4. **Slash command infrastructure + /help + /quit** — `/` prefix detection, command parser, dispatch table
5. **Introspection commands** — `/sig`, `/type`, `/info`, `/list`, `/time`
6. **Startup banner** — language name, help hint
7. **Module-aware prompt** — `{compile}+{eval}ms; {module}>` format, continuation prompt `...`
8. **Stderr routing** — errors to stderr, results to stdout
9. **Special form feedback** — bare `if`, `let`, `fn` show shape description not error

### Debt and quality (1x deferred from S6)

10. **7 Vec RC balance tests** — Vec temporary argument cleanup (non-scope-based dec)
11. **Spec heading annotations** — `[Done]`/`[Rn Sn]` on spec section headings
12. **Missing spec coverage tests** — `#[ignore]` tests for untested in-scope spec sections
13. **QA FIXME test coverage** — U1.3, U1.5, U1.7, U1.6, U1.9
14. **Stale FIXME cleanup** — remove resolved U1.2, U2.1 FIXMEs from roadmap.md
15. **R2.1-R2.3 display fixes** — deftrait display, constrained fn constraint display, impl display

### Deferred to Sprint 8

- **Multi-signature dispatch** — complex feature (13 sketch files), interaction with constrained poly
- **Auto-curry** — depends on multi-sig disambiguation
- Stdlib bootstrap — Ring 3 (needs macros)
- `/expand`, `/mod`, `/reload`, `/mem`, `/run-tests` — Ring 3/4
- `/source`, `/sexp`, `/ast`, `/clif`, `/disasm` — developer introspection, lower priority

## FIXME Debt

| File | Owning Skill | Issue | Deferrals | Resolution |
|------|-------------|-------|-----------|------------|
| `design/arch/roadmap.md:62` | `/typecheck` | U1.2 — parse-int Option return | 0 | **stale** — resolved S6, remove |
| `design/arch/roadmap.md:107` | `/typecheck` | U2.1 — Display trait registration | 0 | **stale** — resolved S6, remove |
| `design/arch/roadmap.md:7` | `/arch` | U0.1 — batch hello-world needs IO | 0 | deferred to Ring 4 |
| `design/arch/roadmap.md:39` | `/qa` | REPL spec non-conformance (12 items) | 0 | **all in scope** |
| `design/arch/roadmap.md:57` | `/backend` | U1.1 — 11 missing string primitives | 0 | deferred to Ring 3 |
| `tests/plan/ring2.md:123` | `/qa` | R2.1 — deftrait display | 0 | **in scope** #15 |
| `tests/plan/ring2.md:128` | `/qa` | R2.2 — constrained fn display | 0 | **in scope** #15 |
| `tests/plan/ring2.md:133` | `/qa` | R2.3 — impl display | 0 | **in scope** #15 |
| `repl/spec.md:56` | `/qa` | U1.6 — poly ADT type var display | 0 | **in scope** #13 |
| `repl/spec.md:61` | `/qa` | U1.9 — poly ADT heap field display | 0 | **in scope** #13 |
| `tests/plan/ring1.md:50` | `/qa` | U1.3 — nested heap ADT RC | 0 | **in scope** #13 |
| `tests/plan/ring1.md:54` | `/qa` | U1.5 — closure capturing heap | 0 | **in scope** #13 |
| `tests/plan/ring1.md:58` | `/qa` | U1.7 — error message quality | 0 | **in scope** #13 |
| `crates/cranelisp-typecheck/plan-typecheck.md:478` | `/typecheck` | Borrow-splitting doc | 0 | deferred |
| `CLAUDE.md:97` | `/spec` | Num trait in spec vs stdlib | 0 | deferred to Ring 3 |
| `repl/spec.md:5` | `/repl` | CLI invocation modes | 0 | deferred to Ring 4 |
| `tests/plan/ring0.md:3` | `/qa` | U0.2 — /learn tutorial engine | 0 | deferred to Ring 4 |

## Architecture Review

**Reviewer**: /arch — **Verdict**: APPROVED WITH CONDITIONS

1. **REPL chrome is sound** — slash command dispatch, prompt, banner, stderr routing will survive into Ring 4. No throwaway infrastructure. The dispatch table is additive; Ring 4 adds commands to the same table.

2. **Multi-sig + auto-curry descoped to Sprint 8** — per /arch recommendation. Complex feature (13 sketch files) with interaction effects (auto-curry + multi-sig disambiguation, multi-sig + constrained poly exclusion). Shipping separately reduces risk. Ring 2 acceptance criteria are met progressively — multi-sig/auto-curry can be Ring 2's fifth increment.

3. **Primitives module** — synthetic module, no file on disk. `discover_module_graph` and `resolve_submodule_file` must early-exit for known synthetic modules. Implicit `(import [primitives [*]])` replaces current copy-from-user seeding.

4. **Cross-module wiring gap** — `pipeline.rs:467` discards `ModuleStructure` (contains `ImportSpec`s). Fix: process imports after dependency compilation, populate cross-module symbol table entries, wire function calls via GOT or JIT imports.

5. **No boundary type changes needed** — existing types sufficient for all Sprint 7 deliverables.

## Skill Plans

### /arch
**Task**: Review sprint scope; confirm REPL chrome and primitives module design
**Approach**: Complete — see Architecture Review above
**Acceptance**: APPROVED WITH CONDITIONS (multi-sig descoped)

### /frontend
**Task**: No reader changes needed this sprint. Slash command detection happens in REPL loop, before reader.
**Approach**: `/` prefix detection is REPL-level (src/repl.rs), not reader-level. No changes to frontend crate.
**Acceptance**: N/A — no frontend work this sprint

### /typecheck
**Task**: Primitives module type environment; stale FIXME cleanup (U1.2, U2.1)
**Approach**: Create `primitives` synthetic SymbolTable in `register_builtins()`. Remove stale FIXME comments from roadmap.md.
**Design refs**: `design/typecheck/`, `design/arch/interfaces.md`
**Acceptance**: Primitives module registered; stale FIXMEs removed

### /backend
**Task**: Cross-module GOT wiring; primitives module codegen support
**Approach**: Process `ImportSpec`s in `compile_module_graph()`. Wire cross-module calls via GOT. Handle `primitives` as synthetic module in module discovery.
**Design refs**: `design/backend/`, `src/pipeline.rs`
**Acceptance**: 4 module tests un-ignored and passing; cross-module calls work end-to-end

### /qa
**Task**: REPL chrome implementation (slash commands, prompt, banner, stderr); REPL qualified display; R2.1-R2.3 fixes; FIXME test coverage; Vec RC tests; un-ignore E2E tests
**Approach**: Implement in `src/repl.rs`: (1) command parser + dispatch, (2) prompt formatter with timing, (3) banner, (4) stderr for errors. Qualified display: format types with module paths, constructors with dot notation. Write FIXME coverage tests.
**Design refs**: `tests/plan/ring2.md`, `repl/spec.md`
**Acceptance**: 20 E2E tests un-ignored and passing; slash commands work; R2.1-R2.3 fixed

### /review
**Task**: Sprint gate review
**Approach**: Code quality, architecture adherence, no regressions after each wave
**Acceptance**: No blockers

### /spec
**Task**: No spec changes needed (multi-sig descoped)
**Approach**: N/A
**Acceptance**: N/A

### /repl
**Task**: Validate REPL chrome against repl/spec.md; add demo scenarios for slash commands
**Approach**: Audit implementation against spec §1-6; add REPL demo script
**Design refs**: `repl/spec.md`
**Acceptance**: REPL display, prompt, banner, slash commands conform to spec

### /stdlib
**Task**: Confirm readiness for Ring 3
**Approach**: Review plan against Ring 2B capabilities
**Acceptance**: Plan current

### /examples
**Task**: No examples changes (multi-sig descoped)
**Approach**: N/A
**Acceptance**: N/A

### /docs
**Task**: Plan REPL commands documentation
**Approach**: Update docs plan with slash command reference
**Acceptance**: Plan updated

### /platform
**Task**: Confirm primitives module doesn't affect platform
**Approach**: Review — synthetic module is separate from platform DLLs
**Acceptance**: No regressions

### /port
**Task**: Validate exemplar against Ring 2B
**Approach**: Review exemplar plan
**Acceptance**: Plan confirmed feasible

## Waves

### Wave 0: Foundation + stale cleanup
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Remove stale U1.2, U2.1 FIXMEs from roadmap.md | **done** | 2 stale FIXMEs removed |
| /qa | R2.1-R2.3 display fixes (deftrait, constrained fn, impl display) | **done** | 3 fixes + 4 tests |
| /qa | QA FIXME test coverage: U1.3, U1.5, U1.7, U1.6, U1.9 | **done** | 21 new tests (14 pass, 5 ignored for known bugs, 2 ignored for Vec) |
| /qa | 7 Vec RC balance tests | **done** | 7 un-ignored; fix: emit_vec_drop_if_temporary() |

### Wave 1: REPL chrome basics (banner, prompt, stderr, /help, /quit)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Slash command infrastructure: `/` detection, parser, dispatch table | **done** | ReplCommand enum + parse_slash_command() |
| /qa | `/help` and `/quit` commands | **done** | |
| /qa | Startup banner (language name + /help hint) | **done** | 2-line banner |
| /qa | Module-aware prompt: `{compile}+{eval}ms; {module}>` | **done** | Timing measured around eval() |
| /qa | Continuation prompt: `...` aligned | **done** | Right-aligned to prompt width |
| /qa | Stderr routing for errors | **done** | eprintln! for errors |
| /qa | Un-ignore: 6 E2E tests | **done** | help, quit, banner, prompt, continuation, stderr |

### Wave 2: Qualified display + primitives module
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Qualified type display: `primitives/Int`, `primitives/Bool`, etc. | **done** | format_type_qualified() + type_modules tracking |
| /qa | Qualified name display: `user/id`, `user/double` | **done** | definition_display with module path |
| /qa | Constructor dot notation: `Color.Red`, `Option.Some` | **done** | format_adt_value() with Type.Ctor notation |
| /qa | Un-ignore: 7 E2E qualified display tests | **done** | int, bool, string, defn, deftype, nullary ctor, data ctor |

### Wave 3: Cross-module wiring
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | Process ImportSpecs in compile_module_graph() | **done** | Shared Jit, register_imports() wired |
| /backend | Wire cross-module calls via GOT | **done** | Single shared Jit across modules |
| /qa | Un-ignore: 4 module integration tests | **done** | qualified, specific, glob, error |

### Wave 4: Introspection commands + special forms
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | `/sig`, `/type`, `/info`, `/list`, `/time` commands | **done** | Full implementations |
| /qa | Special form feedback: bare `if`, `let`, `fn` → shape display | **done** | special_form_feedback() pre-check |
| /qa | Un-ignore: 7 E2E tests | **done** | sig, type, list, info, time, 2x special form |

### Wave 5: Traceability + user-proxy validation
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Spec heading annotations: [Done]/[Rn Sn] | **done** | All spec + repl/spec.md headings annotated |
| /repl | Validate REPL chrome against spec | **done** | 14 findings; 3 high-priority fixed (NC-7, NC-10, NC-12) |
| /docs | Update documentation plan for REPL commands | deferred | Sprint scope already large |

### Wave 6: Sprint gate
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /review | Sprint 7 gate: all tests pass, E2E un-ignored, no regressions | **done** | B1 fixed; I1-I6 tracked as tech debt |

## Notes

- Phase 1 (scope): FIXME scan complete. 691 tests, 32 ignored, 0 failures.
- Phase 2 (arch review): APPROVED WITH CONDITIONS. Multi-sig + auto-curry descoped to Sprint 8.
- Phase 3 (planning): Complete. Skill plans filled.
- Phase 4 (wave organization): Complete. 7 waves organized.
- REPL chrome brought forward per user direction — progressive delivery across waves.
- Wave 0: +24 tests (715 total), -2 ignored (30). Vec RC fix, R2.1-R2.3 fixed, 21 FIXME coverage tests.
- Wave 1: +6 tests (721 total), -6 ignored (24). Banner, prompt, slash infra, stderr routing.
- Wave 2: +12 tests (733 total), -12 ignored (12). Qualified display, dot notation.
- Wave 3: Cross-module wiring with shared Jit, import resolution, qualified name lookup.
- Wave 4: +7 tests (740 total), -7 ignored (5). All 48 E2E tests pass. Full slash commands.
- Wave 5: Spec annotations, REPL validation (14 findings, 3 fixed), clippy blocker fixed.
- Wave 6: Review complete. B1 fixed. I1-I6 tracked for Sprint 8.
- 5 remaining ignored: 2 RC leak patterns, 1 Vec element drop glue, 2 poly ADT type var display.

## Outcome

**Tests**: 740 passing (was 691), 5 ignored (was 32), 0 failures. Net: +49 passing, -27 un-ignored.

### Delivered

**REPL Chrome (brought forward from Ring 4)**:
- Startup banner ("Cranelisp v0.1.0", /help hint)
- Module-aware prompt: `{compile}+{eval}ms; {module}>`
- Continuation prompt: `...` aligned to prompt width
- Stderr routing for errors
- Slash command infrastructure: `/` detection, parser, dispatch table
- `/help`, `/quit`, `/sig`, `/type`, `/info`, `/list`, `/time` — 7 commands
- Special form feedback: bare `if`, `let`, `fn`, `defn`, `deftype`, `match` → shape display
- Bare symbol lookup: functions, operators, types, traits, constructors (spec §4.1)

**Qualified Display**:
- Fully qualified types: `primitives/Int`, `primitives/Bool`, `primitives/Float`, `primitives/String`
- Qualified function names: `user/id`, `user/double`
- Constructor dot notation: `Color.Red`, `(Option.Some 42)`
- Qualified ADT types: `user/Color`, `(user/Option primitives/Int)`
- `type_modules` tracking per type definition

**Cross-Module Wiring**:
- Shared Jit across all modules in `compile_module_graph()`
- Import resolution: `register_imports()` wired to process `ImportSpec`s
- Qualified name resolution: `module/name` splits and resolves via child-then-absolute path
- Qualified aliases for submodule functions

**Debt/Quality**:
- Stale FIXMEs U1.2 and U2.1 removed from roadmap.md
- R2.1 (deftrait display), R2.2 (constrained fn display), R2.3 (impl display) fixed
- 21 QA FIXME test coverage tests (U1.3, U1.5, U1.7, U1.6, U1.9)
- 7 Vec RC balance tests un-ignored (emit_vec_drop_if_temporary fix)
- Spec heading annotations: `[Done]`/`[Rn Sn]` on all spec section headings
- Clippy blocker (approx_constant) fixed

### Deferred

- **Multi-signature dispatch** — descoped to Sprint 8 per /arch recommendation (scope risk)
- **Auto-curry** — descoped to Sprint 8 (depends on multi-sig)
- **Primitives synthetic module** — not yet a proper module (type_modules tracking in REPL serves as interim)
- **6 missing slash commands** (/doc, /source, /sexp, /ast, /clif, /disasm) — need DefEntry storage
- **Error type qualification** (NC-13) — type errors show bare `Int` not `primitives/Int`
- **5 ignored tests**: 2 RC leak patterns, 1 Vec element drop glue, 2 poly ADT type var display
- **Review tech debt**: I1 (compile_and_execute 187 lines), I2 (run_repl 140 lines), I3 (compile_module_graph 135 lines), I4 (discover_module_recursive 117 lines), I5 (build_compile_context 8 params), I6 (complex return type)
- **Documentation plan** for REPL commands

### Findings

1. **REPL chrome is architecturally sound**: All slash command and display infrastructure survives into Ring 4. No throwaway code.
2. **Cross-module wiring required shared Jit**: Per-module Jit would not link cross-module calls. Single shared Jit is the correct approach.
3. **Bare symbol lookup fills a major spec gap**: The self-documentation principle (spec §4.1) requires every valid construct to produce useful feedback. Without bare lookup, functions/operators/types all errored.
4. **Vec element separator was comma, not space**: Spec §1.5 says `[elem1 elem2 ...]` — fixed to space-separated.
5. **Multi-sig + auto-curry descoped correctly**: 13 sketch files, interaction effects with constrained poly. Would have doubled sprint scope.
6. **REPL validation found 14 non-conformances**: 3 high-priority fixed (bare lookup, Vec separator, /type prefix). 6 are missing slash commands (need DefEntry), 5 are lower-priority display refinements.

## Next skills

- `/sprint` — Sprint 8: multi-sig dispatch, auto-curry, primitives module, review tech debt
- `/typecheck` — multi-sig type checking, auto-curry detection
- `/backend` — multi-sig mangled codegen, auto-curry closure compilation
- `/review` — Ring 2 completion gate after Sprint 8
