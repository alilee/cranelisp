---
number: 0029
title: IO trampoline shallow dec uses a `cranelisp-runtime` primitive (`rc::dec_shallow_io`)
status: operative
---

# 0029 — IO trampoline shallow dec uses a `cranelisp-runtime` primitive (`rc::dec_shallow_io`)

Fixing the FIXME at `crates/cranelisp-runtime/src/io.rs:58` requires a shallow single-node RC dec — decrement the RC with Release ordering, on last-ref emit an Acquire fence and dealloc the outer allocation only, do NOT walk fields. This is a distinct primitive from the existing transitive `drop::consume_io_tree` because the trampoline owns only the outer allocation of each intermediate Pure/Effect/Bind/Par node — field pointers are already re-owned by other holders (Bind's inner re-owned as new `current`; Bind's continuation pushed to `cont_stack`; Par's branches consumed by rayon dispatch). `rc::dec_shallow_io` is a genuine Runtime-crate primitive (not throwaway infrastructure) because the "callee consumes only the outer alloc, fields already re-owned" pattern will reappear any time the runtime implements a state-machine walker over an RC-tracked tree. The helper is ~10 lines and exposes the single-node dec as a first-class primitive on `cranelisp-runtime::rc`. This is distinct from the policy question of WHERE to call it (inline in the trampoline loop versus at return — that is a §3.5.4 implementation-detail decision for `/backend`). Canonical location: `crates/cranelisp-runtime/src/rc.rs` (or `drop.rs` alongside `consume_closure`). Owner: `/backend` writes it in Wave 3 alongside the trampoline fix. Rationale: Principle 7 (single source of truth — shallow dec is the Ring 4 dual of the transitive consume; one primitive per concept) + Principle 8 (a genuine primitive, not interim scaffolding — other runtime state-machine walkers can reuse it).
