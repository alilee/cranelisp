---
number: 0011
target: /backend
filed_by: /unknown
filed_at: 2026-05-01
sprint_filed: 64
refers_to: crates/cranelisp-runtime/src/io.rs:173, design/backend/io-trampoline-trace.md §"Post-implementation note (Wave 1)"
status: open
migrated_from_inline: true
---

# 0011 — Thread `SchedulingClass` into the IO Effect node payload

## Issue

The `PlatformEffect.scheduling_class` payload field is currently emitted as `0` at call sites in `crates/cranelisp-runtime/src/io.rs` because the `SchedulingClass` is registered on the platform symbol's `PlatformFn` manifest (see `cranelisp-platform::PlatformFn.scheduling_class`) and is not carried on the Effect IO node itself at runtime. At the trampoline site there is no back-reference to the symbol, so the placeholder is emitted and trampoline events lose the real scheduling class — cross-trace correlation against the scheduler trace is currently required to recover it.

Consider threading `SchedulingClass` into the Effect node payload (extra field) so trampoline events carry the real class without needing cross-trace correlation. Deferred pending Slice 4 evidence; if Slice 4 needs the class, correlate via `/int`'s scheduler trace (which does carry it on the scheduler side) or land the node-payload change then.

## Source location

`crates/cranelisp-runtime/src/io.rs:173` (FIXME body in the `PlatformEffect` emit site, lines 165–177); cross-referenced in `design/backend/io-trampoline-trace.md §"Post-implementation note (Wave 1)"` and `design/review/sprint-61-wave-1-slice-0.md` Important #2.

## Context

```
                // FIXME(/backend): consider threading SchedulingClass
                // into the Effect node payload (extra field) so trampoline
                // events carry the real class without needing a
                // cross-trace correlation. Deferred pending Slice 4
                // evidence.
                io_trace::record_event(
                    IoTraceTag::PlatformEffect,
                    IoTracePayload::PlatformEffect {
                        thunk_ptr,
                        resource_token,
                        scheduling_class: 0,
                    },
```

## Proposed resolution

Either (a) extend the Effect node IR payload with an explicit `SchedulingClass` field threaded from the platform symbol manifest at codegen time, or (b) document that scheduling class must be recovered via cross-trace correlation against `/int`'s scheduler trace. Sprint 61 Wave 1 Slice 0 deferred this once under the one-deferral-permitted policy; ship by Wave 5 or next sprint, else escalate.
