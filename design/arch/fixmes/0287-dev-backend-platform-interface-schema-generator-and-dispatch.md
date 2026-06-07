---
number: 0287
target: /dev (backend)
filed_by: /arch
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/arch/platform-interface.md §5.5 §6.0 §6.2 §6.3 §7.3, design/arch/bounded-contexts.md §3, design/arch/tracing.md §3
status: open
---

# Platform-interface — schema generator + closure walk + GOT-indirect dispatch + startup-object hash baking

## Issue

The platform-interface design (`design/arch/platform-interface.md`, user-ratified
2026-06-07; **normative — read in full**) places three new backend responsibilities, all
grounded in BC §3's "platform-interface codegen role" bullet.

## Scope

1. **The schema generator** (§6.0, §5.5) — a routine that, given a root type set + a
   `SymbolTable`, derives the referenced-ADT set from `DefKind::PlatformEffect` sig schemes,
   takes the **transitive closure** over field types (nested ADTs in; scalar leaves out),
   substitutes concrete type args for instantiations, and emits the schema artifact:
   `Map<FQTypeName, Vec<(CtorName, tag, Vec<(Symbol, FieldType)>)>>` text (concrete
   instantiations keyed by the structured type expression, not a mangle) + a canonical
   `;; layout-hash:` header. It MUST **share the closure-walk + concrete-instantiation
   substitution with the trace `DisplayDescriptor` baker** (the shared asset is the *walk*,
   not a single serialized output form — different consumers/lifetimes/serializations; do
   NOT force one representation). One generator, multiple callers (int's `/platform-schema`
   command + load-time check; the `--link` recompute below).
2. **The platform GOT-indirect call arm** (§6.2, §6.3) — a `DefKind::PlatformEffect` call
   site emits GOT-indirect dispatch against the DLL's exported `__cranelisp_got_platform_<name>`
   at the entry's `got_slot`, referenced as a `Linkage::Import` data symbol (resolved by
   `dlsym` in JIT / `ld` in `--link`), structurally identical to user-module GOT dispatch —
   replacing the direct `Linkage::Import`-against-mangled-`jit_name` path (`apply.rs:209-227`).
   Backend does NOT emit the platform GOT (the DLL exports it).
3. **Startup-object hash baking** (§6.0, §7.3) — for `--link`, regenerate the schema from
   the `.cl` modules the compiler compiled, hash it, and bake the hash into the startup
   object (exe-bundle path); the startup stub compares it against the statically-linked
   `__cranelisp_layout_hash_<name>` at process start, aborting with rebuild guidance on
   mismatch.

## Acceptance

- The generator is reachable from both a REPL-driven call (int) and the `--link` codegen
  path; the closure-walk is one routine shared with the descriptor baker (no duplication).
- Platform call sites emit GOT-indirect dispatch in JIT, cache-restore, and `--link` — the
  same `Linkage::Import`-against-`__cranelisp_got_platform_<name>` reference in every CLIF.
- The `--link` startup stub bakes + compares the layout hash; mismatch aborts at process
  start with rebuild guidance.
- `cargo public-api` baseline for `cranelisp-backend` regenerated; BC §3 + the source
  rustdoc name the generator + dispatch arm.

## Context

Backend half of the platform-interface cascade. Pairs with 0286 (platform macro), 0288 (int
load path + command), 0289 (qa e2e). Supersedes the backend half of the re-pointed 0232.
