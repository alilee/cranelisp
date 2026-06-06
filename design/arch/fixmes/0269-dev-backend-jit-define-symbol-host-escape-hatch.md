---
number: 0269
target: /dev
filed_by: /arch
filed_at: 2026-06-06
sprint_filed: 76
target_sprint: 77
refers_to: design/arch/test-discovery.md §6 "Backend — `Jit::define_symbol`" + §6 "Backend — one kind-dispatched call arm", design/arch/bounded-contexts.md §3 invariant 8, crates/cranelisp-backend/src/jit.rs (Jit::new / symbol_lookup_fn)
status: open
---

# Backend: `Jit::define_symbol` host-symbol escape hatch + `PrimitiveExtern` call-dispatch arm

Successor to the deleted FIXME 0261 (the parked-test-intrinsic JIT-resolution gap)
— the settled test-discovery design answers 0261's parked a/b/c with neither verbatim:
the resolution is an additive host-symbol escape hatch (`Jit::define_symbol`) plus the
`DefKind::PrimitiveExtern` entry kind (already landed in `cranelisp-types` this sprint).
Crate: `cranelisp-backend` (`/dev` narrow, backend mode). Normative spec:
`design/arch/test-discovery.md` §6.

## Scope

1. **`Jit::define_symbol(name: &str, ptr: *const u8)`** — a post-construction inserter
   over the mutable map the JIT's `symbol_lookup_fn` already consults at module
   finalization (`jit.rs` ~:297). When an unresolved `Linkage::Import` relocation
   against `name` is settled, the lookup returns `ptr`. Additive only — NO forked
   constructor (Principle 11), no callback indirection, no registry. `Jit::new`'s
   derived-from-`symbol_tables` default stands; this is the documented escape hatch for
   host-promised symbols whose body is neither codegen-emitted, bundled
   (`cranelisp-primitives`), nor catalogued (`intrinsics_table()`). See BC §3 invariant 8.
2. **The `PrimitiveExtern` call-dispatch arm (the third call-dispatch arm).** A callee
   whose `ModuleEntry::Def` carries `kind: DefKind::PrimitiveExtern` lowers as a
   `Linkage::Import` against the entry key (the symbol-table key IS the ABI name) —
   identical in shape to the platform-effect / intrinsic import path, NOT a GOT-indirect
   call. Make sure this arm exists (it is the call shape for `discover-tests`); it does
   not exist today because the variant is brand-new.
3. **No friendly `--link` rejection.** A `--link` build of a program calling
   `discover-tests` emits its `Linkage::Import`; the missing host symbol surfaces as an
   unresolved-symbol link/load error (interim — §4.5). Do not add a compile-time
   diagnostic.

## Acceptance

- `Jit::define_symbol` exists and a `discover-tests` `PrimitiveExtern` call resolves at
  JIT-finalize after int promises it (cross-check with FIXME 0271's session-init call).
- A `PrimitiveExtern` callee lowers `Linkage::Import` against its key; unit coverage for
  the call-shape arm lives in the backend crate (`/dev` owns unit tests).
- `intrinsics_table()`-backed `catch-runtime-error` needs NO backend change here — it is
  resolved by the existing intrinsic-import path (invariant 6); confirm by absence.
- Workspace green; backend `public-api.txt` regenerated if the surface changes
  (`Jit::define_symbol` is a new pub fn — expect a one-line baseline delta).
