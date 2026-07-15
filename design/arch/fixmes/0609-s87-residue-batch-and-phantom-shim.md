---
number: 0609
target: /dev
filed_by: /sprint
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S110
refers_to: src/ S87-residue batch (dead-code allows, extra_jit_symbols vestige,
  production unwrap) + the phantom_member_diagnostic shim reachability question
  (/qa or /design typecheck for the verdict). Narrow-deploy /dev to src/.
status: open
---

# S87 residue batch + the untracked phantom-shim question

## Source

S109 `src/` whole-context audit (`audits/src-s109.md` R-5), **ACCEPTED** S110 Phase 1.
Precedent: the S108 typecheck R-5 residue batch, accepted as FIXME 0581.

## Evidence (quoting the assessment §2.7/§2.8)

- **F-H dead accessors** — `introduce_module_blank` (`session_v4/lifecycle.rs:620-621`),
  `cached_module_remove` (`scheduler.rs:2000-2001`); ~30-site `allow(dead_code)`
  population (module-level allow on `cache_writer.rs:13`; clusters in `redefine.rs` (7),
  `platform.rs` (3)). The S87 Wave-0 "prefer deletion" precedent was not applied.
- **F-I** — vestigial raw-pointer param `extra_jit_symbols: &[(String, *const u8)]`
  threaded through `inline_jit_codegen_for_module/_for_names`, nulled at `worker.rs:1125`
  — a dead `*const u8` slice is a latent foot-gun.
- **F-K** — production `.unwrap()` at `process_form.rs:906`
  (`ctx.symbol_tables.get(&ctx.current_module).unwrap()`); `src/CLAUDE.md` §Error
  Handling forbids it.
- **Phantom-shim question** — `phantom_member_diagnostic`'s comment
  (`process_form.rs:438-449`) defers "the deeper ordering cure" to a `/typecheck` FIXME
  that was **never filed**; post-0571 (member-absent now gaps unconditionally) it is
  unverified whether the phantom-child shape can still arise, i.e. whether this shim is
  live or dead.

## Done (assessment §3 R-5)

Each `allow(dead_code)` deleted or justified with its consumer named; the vestigial param
dropped; the unwrap converted to `unreachable!("invariant: …")`; the phantom shape either
reproduced (→ tracked FIXME for the typecheck probe-order cure) or shown unreachable
(→ shim + its `find_named_var_span` helpers deleted). The shim verdict is genuine unknown
work — `/qa` or `/design` (typecheck) rules reachability; `/dev` (src/) executes the residue.
