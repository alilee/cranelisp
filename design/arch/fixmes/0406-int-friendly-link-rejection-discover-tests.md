---
number: 0406
target: /int
filed_by: /arch
filed_at: 2026-06-17
sprint_filed: 86
refers_to: design/arch/test-discovery.md §4.5 (S86 D5a ruling), §5 "What retires", §6 "Int — bootstrap publication"; design/arch/bounded-contexts.md §6 (int — --link standalone executable generation); crates/cranelisp-backend/src/compiler/apply.rs (the PrimitiveExtern Linkage::Import arm); tests/link.rs::link_module_referencing_discover_tests_extern_resolves_at_aot_link
status: open
---

# Friendly compile-time rejection for a REPL-only `PrimitiveExtern` (`discover-tests`) reaching `--link`

## Issue

`discover-tests` is a `DefKind::PrimitiveExtern` whose body is host-promised only in a
**live session** (int's `Jit::define_symbol` at session-init, REPL/`--run`). Under AOT
`--link` there is no live session, so the emitted `Linkage::Import` against
`discover-tests` is never satisfied → the `cc` link step fails with a **raw linker
error** `undefined reference to discover-tests`, exit 1, no executable produced.

This is the **documented interim behaviour** (`test-discovery.md` §4.5: "No friendly
rejection (settled) … a future sprint may add a friendly diagnostic"). The S86 D5a
ruling (test-discovery.md §4.5) **reaffirmed the interim for S86** and selected
disposition (c) (raw error stands; `/qa` corrects the repro to assert link-failure). It
explicitly **deferred** the friendly rejection — disposition (b) — to a future sprint as
this FIXME.

The raw linker error is exactly the kind of opaque failure the project Design Principle
(root `CLAUDE.md`: "No valid language construct should produce an opaque error";
self-documenting feedback) opposes. A user who writes a perfectly valid program that
calls `discover-tests` and runs `cranelisp --link` deserves a clear message naming the
cause, not a `cc` linker diagnostic about an internal symbol name.

## Proposed resolution

Add a **compile-time gate** in **int** (`src/`) — the surface that owns `--link`
standalone-executable generation (bounded-contexts.md §6) and is the only surface that
knows the build *mode* (REPL / `--run` / `--link`) and assembles the link set. Backend
lowers the `Linkage::Import` blind to mode (apply.rs); int is the seam that can refuse
before invoking `cc`.

Sketch of the gate (int to design the precise shape via `/design` + `/dev`):

- During `--link` artifact assembly (after typecheck/codegen, before the `cc`
  invocation), scan the modules pulled into the link for any **referenced
  `DefKind::PrimitiveExtern` whose body is dev-session-promised** (today: the
  `discover-tests` family). The kind discriminator + the absence of a `define_symbol`
  promise in the AOT path is the structural signal — prefer a kind/metadata predicate
  over a name match so the gate generalizes to any future REPL-only extern (do NOT
  hard-code the string `discover-tests` if a `DefKind`/flag predicate is available).
- Emit a friendly `CranelispError` (compile-time, exit non-zero) along the lines of:
  `` `discover-tests` is a REPL/dev-session-only builtin and is not available in
  `--link` builds (it scans the live session's symbol table, which a standalone
  executable does not have). Remove the reference or run this program with `--run` /
  the REPL.`` — naming the symbol, the reason, and the remedy.
- This **replaces** the raw `cc` `undefined reference to discover-tests` with a clear
  diagnostic surfaced before linking. `catch-runtime-error` is unaffected (it resolves
  in `--link` — self-contained intrinsic); the gate must NOT reject it.

Scope: int-only (one crate seam). No change to the settled "dev-session-only" semantics
— this is purely a *better error*, not new resolution capability. Disposition (a)
(resolving `discover-tests` under `--link`) remains off-limits without a user
re-convergence of the fourth-convergence design.

## Operational implication / Context

- **Test handoff.** `/qa` owns `tests/link.rs::link_module_referencing_discover_tests_extern_resolves_at_aot_link`.
  For S86 (this FIXME deferred) the repro asserts the **interim**: non-zero exit
  (`assert_failure`) + an output substring naming `discover-tests` (the raw linker
  error). When this FIXME lands, `/qa` **retargets the same repro** to assert the
  **friendly** message instead of the raw linker error: still non-zero exit, still names
  `discover-tests`, but the assertion shifts from the `cc` `undefined reference` /
  `Symbol not found` phrasing to the friendly compile-time diagnostic's phrasing (e.g.
  "REPL/dev-session-only" + "not available in `--link`"). The `assert_failure` half is
  stable across the transition; only the message substring changes.
- **Design fidelity.** `test-discovery.md` §4.5 / §5 already anticipate this ("a future
  sprint may add a friendly diagnostic"); landing it does not reopen the settled design,
  it discharges its named follow-up. When this lands, `/arch` updates §4.5 to record the
  diagnostic as delivered (interim → friendly) and §5 "What retires" stays accurate
  (the friendly rejection is now present, not absent).
- **Generality.** Prefer a kind/metadata-driven predicate so any future REPL-only
  `PrimitiveExtern` inherits the friendly rejection without a per-name edit.
