---
number: 0507
target: /design (src/)
filed_by: /sprint
filed_at: 2026-07-03
sprint_filed: 102
refers_to: design/int/session-transaction.md §9.1.1, design/int/s102-defect-wave.md §1/§7.1, repl/spec.md §18.1.1
status: open
---

# T1 trigger route + 0491 exclusion — two design-argument holes found by the Wave-4 review

Both fixes conform to their designs; the holes are in the designs' arguments. Full evidence: S102 Wave-4 /review report (SPRINT.md §Notes Wave-4 entries).

## Issue 1 — F2: route-based T1 trigger over-fires for slotted→slotted late-binding targets

`is_t1_downgrade()` (`prior_was_def && !per_symbol && !gate_exempt`) reads no slot information. For a slotted prior replaced by a slotted staged entry outside per-symbol precision — reachable shape: `deftype` re-entry, ctors are slotted `DefKind::Constructor` Defs — the commit reuses the prior slot and the turn patches code in place. Compiled callers dispatch through the GOT slot and DO pick up the new definition at next call, yet `stale_callers` names them. That violates §18.1.1's negative MUST ("must not name any symbol that picks up the new definition at its next call"). The design's "route, not diff" ruling was argued only from templates/mints.

**Proposed resolution**: rule on the slot refinement — trigger additionally requires `o.new_slot.is_none() || o.old_slot.is_none()` (keeps every designed cell: slot-less staged = displacement/template shapes; slot-less prior = concrete-over-template mint-staleness). If ruled in, /qa adds the ctor-target e2e cell; the existing unit `t1_downgrade_trigger_route_cells` needs no rewrite (fixture has both slots None). Must resolve before §18.1.1 spec rows are annotated `[Tested+Neg]` / before sprint close.

## Issue 2 — F3: 0491's frozen-world safety argument covers `__expr` but is asserted for all gate-exempt internals

`ReverseIndex::build` excludes every `is_gate_exempt_internal` name as caller. The safety argument — "a stale wrapper is never re-invoked; each expression turn redefines it before invoking" — is true of `__expr` only. A compiled macro clause (`__macro_{name}_clause_{idx}`) persists and IS re-invoked at the next expansion. If a clause body can reference a cross-module user fn (the locked model forbids only same-module non-macro callees), an AbiChanging redefinition of that fn now neither re-typechecks nor traps the clause and is invisible in `stale:` — silently stale expansion path.

**Proposed resolution**: one reachability confirmation against the macro-availability model. If reachable: narrow the build-level exclusion to `__expr*` (or add clause edges back with a distinct grain). If unreachable: record the argument in §7.1 and this closes as Minor. Related pre-check for Wave 7: `/refs`' textual-scan leg must cover macro-clause references that the index leg now hides.

## Issue 3 — F5a (rider, pinning note only)

defmacro turns return early (`eval.rs:329`) before `apply_redefinition_outcomes`, so macro-target outcomes are dropped — currently moot (macro heads have no reverse edges) but the S103 module-grain cure should carry a note that the T1 route cannot fire for macro targets today.

## Addendum (filed_by /sprint, post-Wave-5, 2026-07-03)

Two more /design(src/) items from the Wave-5 dev pass, same drain:

4. **Startup-load exception pin**: `recover_startup_failure` (CS-0489) drains `pending_cascade_reports` — the degraded re-drive against a warm table classifies Def-over-Def outcomes but startup is a load, not a user redefinition turn, so `stale:`/cascade sections are suppressed. Record in `session-transaction.md` §9.1.1 as the startup-load exception.
5. **§5.2 correction in `s102-defect-wave.md`**: the claim "today `error_modules` gates nothing" is wrong — the §14.4 gate WAS wired in `process_commands` (it gated everything, including definitions); the actual Wave-5 change was the §18.8 definition carve-out (`is_repair_definition_turn`, watcher-path included). Reconcile the doc with as-built.

## Operational implication

Issues 1–2 gate the §18.1.1 `[Tested+Neg]` annotation and should resolve within S102 (a small /design(src/) disposition, then /qa cells + possible one-line /dev predicate change). Not blocking Waves 5–8.
