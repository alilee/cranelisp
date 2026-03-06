# Sprint 7: Ring 2B Completion — Cross-Module Wiring, REPL Display, REPL Chrome

**Status**: DRAFT
**Ring**: 2 (Abstraction) — fourth increment
**Goal**: Complete Ring 2B by wiring cross-module imports end-to-end, implementing qualified REPL display, adding REPL chrome (slash commands, banner, prompt), and delivering multi-sig dispatch.

## Scope

Sprint 6 delivered module infrastructure (extraction, type scoping, GOT, orchestrator, graph discovery) but cross-module calls are not yet end-to-end wired. This sprint completes Ring 2B.

### Carried from Sprint 6

1. **Cross-module import resolution** — wire export registration in orchestrator, un-ignore 4 module tests
2. **REPL qualified display** — output `primitives/Int`, `user/id`, `Color.Red` notation, un-ignore 9 E2E tests
3. **REPL chrome** — slash commands (/help, /quit, /list, /sig, /info, /type, /time), banner, stderr routing, special form feedback, un-ignore 11 E2E tests
4. **7 Vec RC balance tests** — Vec temporary argument cleanup (non-scope-based dec)
5. **Spec heading annotations** — `[Done]`/`[Rn Sn]` on spec section headings
6. **Missing spec coverage tests** — `#[ignore]` tests for untested in-scope spec sections
7. **QA FIXME test coverage** — U1.3, U1.5, U1.7, U1.6, U1.9

### New scope

8. **Multi-signature dispatch** — `(defn show ([Int x] ...) ([Bool x] ...))` type detection + dispatch resolution + backend mangled codegen
9. **Auto-curry** — `(map (+ 1) [1 2 3])` partial application
10. **Primitives module** — proper `primitives` synthetic module replacing current "user" module seeding hack
11. **Stdlib bootstrap** — begin writing `lib/` modules now that module infrastructure exists

## Next steps

Invoke `/sprint` to run Phase 1 (FIXME scan + state assessment) and Phase 2 (arch review).
