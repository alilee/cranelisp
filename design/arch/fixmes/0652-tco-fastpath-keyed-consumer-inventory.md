---
number: 0652
target: /arch
filed_by: /design (backend)
filed_at: 2026-07-19
sprint_filed: 113
refers_to: design/arch/backend-keyed-consumer.md §3 (per-site inventory S1–S24) + §4 (wave-plan narrative); crates/cranelisp-backend/src/compiler/apply.rs:176-184 (TCO fast-path 1)
status: open
---

# Name the TCO self-call fast-path as a covered keyed-read site in the keyed-consumer inventory

## Why (arch ruling, SPRINT.md §Notes 2026-07-19)

`compile_apply`'s TCO fast-path 1 (`apply.rs:176-184`) decided self-call by BARE
written-name equality (`*name == *fn_name`) before consulting the carrier — a
name-equality-as-identity judgment (BC §3 invariant 10 / Principle 24 class) that
bypasses the keyed-consumer discipline. It **survived the S110 W1–W3 resolver
excision because it is neither a `resolve_*` call nor a `symbol_tables.iter()`
scan**, so the §3 per-site inventory (S1–S24) and the §707 grep gate never counted
it. The S113 W2 backend change-set fixes it to key on the callee
`MonoExpr::Var.resolved_target == the current fn's storage FQ (module+symbol)` —
i.e. it becomes a genuine keyed-read site. Full fix design + case list + spec-diff:
`design/backend/backend.md §2.7.1`.

## The ask (arch-owned doc surface)

`design/arch/backend-keyed-consumer.md` is `/arch`-owned (arch/ tree); `/design`
(backend) may not edit it. Requested update:

1. **§3 per-site inventory** — add a row (S25, or a NOTE) for the TCO self-call
   fast-path (`apply.rs` fast-path 1): kind = self-call TCO gate; carrier =
   callee `Var.resolved_target` compared against the current fn's storage FQ
   (`{ctx.current_module, current_fn_name}`); wave = S113 W2. It reads a carrier
   rather than calling a resolver, so it is not caught by the §707 grep gate (which
   targets `resolve_*`/`lookup_constructor`) — record that it is a keyed-read site
   the grep pattern does not cover, so a future audit counts it deliberately.
2. **Fast-path 2 note** (for completeness) — the SigDispatch mangled-name arm of
   `is_self_call` (`fn_compiler.rs:1512`) needs NO backend change, but its soundness
   is **truthfulness-conditional**, not merely module-safe: the 0519 `{home}/{bare}$sig`
   mangle embeds the module (necessary), but the load-bearing guarantee is that the
   PRODUCER never records a self-`SigDispatch` for a shadowed call — established by the
   W2b arch REDIRECT ruling (producer-side, SPRINT.md §Notes "/arch fp2 ruling:
   REDIRECT"; the Phase-3 "module-safe, no change" verdict was empirically falsified
   by the polymorphic-shadow hang). Worth a one-line note beside the inventory row so
   fp2 is documented as a carrier-adjacent read whose safety rests on producer record
   truthfulness (P24), not on the backend re-checking locals.

No behavioural or interface consequence — a documentation-currency update so the
keyed-consumer inventory is complete. The archive-move of the doc is parked
(SPRINT.md §8); this row can land at the same archive-triage pass or earlier.
