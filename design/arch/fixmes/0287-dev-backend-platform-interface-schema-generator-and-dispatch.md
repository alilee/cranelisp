---
number: 0287
target: /dev (backend)
filed_by: /arch
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/arch/platform-interface.md §5.5 §6.0 §6.2 §6.3 §7.3, design/arch/bounded-contexts.md §3, design/arch/tracing.md §3
status: backend-landed (S76 W4a /dev backend) — cross-crate seams residual
---

## Progress note (S76 Wave 4a — /dev cranelisp-backend)

All three BACKEND responsibilities are landed in `cranelisp-backend`; the
remaining work is cross-crate (int 0288 + platform 0286 flips + one intrinsics
body) and is named below as residual. KEEPING this FIXME open until the seams
connect end-to-end (qa 0289).

**Landed (backend, tested, baseline-regenerated):**

1. **Schema generator** — `crates/cranelisp-backend/src/schema.rs` (new `pub`
   module). `generate_schema(symbol_tables, roots) -> String` (text + `;;
   layout-hash:` header), `compute_layout_hash(symbol_tables, roots) -> String`
   (the check side), `platform_effect_roots(platform_table) -> Vec<Type>` (derive
   roots from `DefKind::PlatformEffect` sig schemes). Shape =
   `Map<structured-type-expr, Vec<(CtorName, tag, Vec<(Symbol, FieldType)>)>>`,
   S-expr text (one parser), concrete instantiations keyed by the structured type
   expression (NOT a mangle, §5.5.3). **Shared closure-walk:** the substitution
   primitives (`collect_var_ids`, `subst_for_ctor_fields`) now live ONCE in
   `schema.rs`; `compiler/trace_codegen.rs::build_adt_subst` consumes them — the
   walk is one routine, two emitters (descriptor blob / schema text), per the
   "share the walk, not the output form" instruction (§6.0). 4 unit tests.
2. **Platform GOT-indirect call arm** — `compiler/apply.rs` (the
   `BuiltinFn` "unrecognized builtin" arm + the `compile_direct_call` path both
   route through `resolve_got_target`). **Transitional discriminator:**
   `resolve_got_target` resolves a `DefKind::PlatformEffect` entry IFF it carries
   the NEW `got_slot: Some(_)` shape (adopted from the DLL-exported GOT) → emits
   GOT-indirect against `__cranelisp_got_platform_<name>`; the as-built
   `got_slot: None` shape misses it and stays on the direct-extern-against-
   `jit_name` path. No mode fork, no flag (Principle 11) — the arm activates
   automatically when int/platform flip to the DLL-exported-GOT model. 1 unit
   test (`platform_effect_new_shape_resolves_got_indirect`).
3. **Startup-object hash bake** — `crates/cranelisp-backend/src/exe.rs`:
   `pub struct PlatformLayoutCheck { name, expected_hash }` +
   `generate_startup_object_checked(.., &[PlatformLayoutCheck])`. The stub bakes
   the compiler-computed expected hash + name as `.rodata`, declares the linked
   `__cranelisp_layout_hash_<name>` as imported data, and calls
   `cranelisp_check_layout_hash(linked, expected, name)` before `main` — abort on
   mismatch. The 3-arg `generate_startup_object` stays a back-compat wrapper
   (empty checks). 2 unit tests.

**What int (0288) calls (the seam, documented in the `generate_startup_object_checked`
rustdoc):** int's `--link` exe-bundle driver computes the per-platform hash via
`cranelisp_backend::schema::compute_layout_hash` over the modules it compiled,
builds a `PlatformLayoutCheck` per linked platform, and passes the slice. int's
`/platform-schema` command + session-load hash check are thin callers of
`schema::generate_schema` / `compute_layout_hash`.

**RESIDUAL (cross-crate, NOT backend; tracked for connect-up):**

- **Runtime intrinsic owed (intrinsics-crate, NOT backend): LANDED (S76 W4a
  /dev intrinsics, folded into FIXME 0270).** The
  `cranelisp_check_layout_hash(linked: *const u8, expected: *const u8, name:
  *const u8)` extern — strcmp the NUL-terminated hashes, on mismatch print
  `"platform '<name>' layout hash mismatch — run /platform-schema <name> and
  rebuild"` + `abort()`. Now lives in `crates/cranelisp-intrinsics/src/layout.rs`
  (`#[export_name = "cranelisp_check_layout_hash"]`), with unit coverage
  (matching-hashes-return + byte-comparison-exact; the abort path can't be
  exercised in-process). Force-linked via `cranelisp-exe-bundle`'s
  `pub use cranelisp_intrinsics::layout` re-export. Not in `intrinsics_table()`
  by design (startup-only symbol, like `cranelisp_init_primitives`/`exit`).
  Backend already declares + calls it (this FIXME's startup-stub work).
- **The new-shape activation depends on int 0288** (build SymbolTable with
  `got_slot = manifest index` + GotTable wrapping the DLL-exported GOT) and
  **platform 0286** (the macro emits `__cranelisp_got_platform_<name>`). Until
  then the as-built direct-extern path stays live (the arm is dormant).
- **q-tag-stability (§2.2):** confirmed source-positional in the schema walk
  (tags read from `DefKind::Constructor.tag` / product tag 0 — declaration
  order); two runs over identical resolved source produce byte-identical text +
  hash (`layout_hash_is_stable_and_change_sensitive` test).
- **q-schema-grammar (§2.2):** the generator emits an S-expr form so the existing
  frontend reader can be the DLL-side parser (recommendation followed); the
  platform-crate parser repoint is platform 0286's work.

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
