---
number: 0043
title: Runtime splits into `cranelisp-primitives` + `cranelisp-intrinsics`; backend has no trait knowledge
status: pre-implementation
filed: sprint 65 (Phase 2 legacy triage)
canonical_location: design/arch/legacy/substance-scoping.md §1.7 (substantive resolution); to be implemented across `crates/cranelisp-primitives/` (new), `crates/cranelisp-intrinsics/` (new), `crates/cranelisp-runtime/` (retires), `crates/cranelisp-backend/src/operators.rs` (renames to `primitives_inline.rs`; trait-knowledge maps deleted), stdlib trait impls
amends: []
amended_by: []
retracts: [0014]
reframes: [0015]
filed_by_fixme: 0150
---

# 0043 — Runtime splits into `cranelisp-primitives` + `cranelisp-intrinsics`; backend has no trait knowledge

## Statement

Two builtin categories are formally distinguished and live in two separate crates:

- **Primitives** (e.g., `add-i64`, `int-to-string`, `parse-int`): callable from user code via the `primitives/` module path. Live in **`cranelisp-primitives`** crate as `extern "C"` Rust fns. Symbol-table entries at `primitives/<name>` with GOT slots; addressable as values. Backend MAY substitute CLIF inline at direct call sites via a name-keyed substitution table.
- **Intrinsics** (e.g., `rc_inc`, `rc_dec`, `dec_shallow_io`, drop glue, allocator, `runtime_panic`, IO trampoline): NOT callable from user code; not in symbol table; not in GOT. Live in **`cranelisp-intrinsics`** crate as `extern "C"` Rust fns. Backend emits direct extern calls; resolved via JIT intrinsic registration (REPL/`--run`) or system linker (`--link`).

Backend's inline-primitive substitution table is keyed on `Symbol` (e.g., `add-i64`) only — **NO trait-knowledge keys** (no `(TraitName, Symbol, TypeName)` triples). Trait dispatch resolves at typecheck/stdlib level; the resolved target (a stdlib defn for the impl) is what backend compiles; the impl body calls primitives by name; backend substitutes from there.

**Decision 14 retracts.** Its premise — "backend recognizes known primitive impls (e.g., `Num.+$Int` → `iadd`) via a static `(TraitName, Symbol, TypeName) → PrimitiveOp` mapping" — is rejected; backend has no trait knowledge. (Decision 14 was already deleted from the register in commit `754d525`; this Decision is the formal replacement that supersedes its direction. Git carries the historical body.)

**Decision 15 reframes.** The "two resolution paths" pattern is correct in **typecheck** (Ring 0–1 `BuiltinFn` coexists with Ring 2 `TraitMethod`) but the implication that **backend** has two paths is wrong. Backend has ONE path: resolve a call's target name; if the name matches an inline primitive (per backend's name-keyed substitution table), substitute CLIF; otherwise emit a call. Trait dispatch is invisible to backend by the time the resolved target is in hand. (Decision 15 was likewise deleted in commit `754d525` once its anchor was gone; this Decision reframes its correct half explicitly.)

## Rationale

The current architecture violates **Principle 1 (decoupling — surfaces evolve independently)** and **Principle 7 (no duplicate addressable forms)**:

- `cranelisp-backend/src/operators.rs:323–394` literally maps `("Num", "+", "Int") => Some("add-i64")`, `("Display", "show", "Int") => Some("int-to-string")`. Backend special-cases trait names. Every new trait the language defines that wants primitive-backed impls would require a backend change.
- `cranelisp-backend/src/compiler/literals.rs:327–332` carries a parallel `"+" => Some("cranelisp_op_add")` map for operator-as-value.
- `cranelisp-runtime/src/primitives/int.rs` exposes both `add-i64` (the named primitive substituted to inline CLIF) AND `cranelisp_op_add` (a separately-named extern fn for the operator-as-value case) — duplicate forms that drift independently.
- `cranelisp-runtime` BC §4 bundles two conceptually distinct categories — language-level callable primitives + backend-emitted-call targets — under one bounded context, accreted from convenience. Categories have different evolution drivers (spec-driven vs backend-driven) and `/dev` ownership is unclear.

The corrected model:
- Trait dispatch resolves at typecheck/stdlib (Decision 4 family + ImplRegistry-on-SymbolTable per the now-landed Sprint 51 work). When typecheck resolves `(+ 1 2)` to `Num.+$Int`, that Decision-binding name routes through the stdlib `(impl Num Int)` body, which calls `(add-i64 a b)`. Backend sees a call to `add-i64` and may inline; backend never sees `Num.+$Int`.
- Operators-as-values (`(let [f +] (f 1 2))`) go through the `+`-resolution-to-`add-i64` path the same way; the `cranelisp_op_*` parallel forms are duplicate addressable forms that delete.
- Physical separation between "what runs" (`cranelisp-primitives` + `cranelisp-intrinsics`, both linked into deployed binaries) and "what compiles" (`cranelisp-backend`'s codegen logic) makes deployment artefacts self-evident: a `--link` binary depends on the two runtime-side crates and not on backend.

Rejected alternatives:

- **Keep one runtime crate, fix the backend trait-knowledge maps in place.** Rejected: the BC ambiguity (which category does this symbol belong to?) is the structural problem; deleting the maps without splitting the crate leaves the BC muddled and the `cranelisp_op_*` duplicates without a principled home.
- **Fold intrinsics into backend.** Rejected: backend's BC is "Typed AST → executable code"; intrinsics are runtime support code with stable ABI contracts, not codegen logic. Cohabitation would re-create the BC overlap that this Decision corrects.

## Bounded-context shift

`bounded-contexts.md` §4 retires; replaced by §4a + §4b:

```
§4a Primitives — `cranelisp-primitives`
  Bounded context: language-level callable surface; spec-defined operations;
  user code references via `primitives/<name>`. Symbol-table entries; GOT
  slots; addressable as values. Backend MAY substitute inline at direct call
  sites; otherwise emits normal calls (GOT-indirect). Owned by /dev narrow per
  crate. Spec-driven evolution.

§4b Intrinsics — `cranelisp-intrinsics`
  Bounded context: backend-emitted-call targets; runtime support code. NOT
  callable from user code; not in symbol table; not in GOT. Backend emits
  direct extern calls; ABI tightly coupled to backend's codegen choices.
  Owned by /dev narrow paired with /dev (backend). Backend-driven evolution.
```

## Migration scope

| Today (`cranelisp-runtime/src/`) | Goes to |
|---|---|
| `primitives/{int,float,bool,mod}.rs` (Cat 1: language-level callable) | **`cranelisp-primitives`** |
| `rc.rs` (Cat 2: RC inc/dec) | **`cranelisp-intrinsics`** |
| `drop.rs` (Cat 2: consume_*, drop glue) | **`cranelisp-intrinsics`** |
| Allocator (Cat 2: `cranelisp_alloc` etc.) | **`cranelisp-intrinsics`** |
| `io.rs` (Cat 2: trampoline) | **`cranelisp-intrinsics`** |
| `panic.rs` (Cat 2: `runtime_panic`) | **`cranelisp-intrinsics`** |
| IoObserver registration API (per Decision 40) | **`cranelisp-intrinsics`** (intrinsic-extension hook) |
| `io_trace.rs` (per Decision 40) | `src/io_trace/` (int) |
| `trace.rs` (per Decision 40) | `src/trace/` (int) |

**Concrete code deletions and refactors:**

- Delete `cranelisp_op_add … cranelisp_op_ge` (10 extern fns) from `cranelisp-primitives` (the relocated runtime) — `add-i64`, `sub-i64`, etc. ARE the addressable form via their `primitives/<name>` symbol-table entries.
- Delete `cranelisp-backend/src/operators.rs:323–394` (`(Trait, method, Type) → primitive-name` map).
- Delete `cranelisp-backend/src/compiler/literals.rs:327–332` (`"+" → "cranelisp_op_add"` map).
- Rename `cranelisp-backend/src/operators.rs` → `cranelisp-backend/src/primitives_inline.rs`; the surviving substitution table at line 38 (`"add-i64" => iadd`) is name-keyed only.
- Audit stdlib's `(impl Num Int)`, `(impl Display Int)`, `(impl Eq Int)`, `(impl Ord Int)` — each impl body calls the primitive directly (`(defn + [a b] (add-i64 a b))`); refactor where the impl was relying on backend's collusion.
- Update `crates/cranelisp-backend/src/jit.rs` `IntrinsicSymbol` array: remove `cranelisp_op_*` entries; keep `int-to-string` etc. as legitimately-registered intrinsics (the addressable backing for those primitives' GOT slots, until/unless those primitives also gain inline substitution).

## Cross-references

- `design/arch/legacy/substance-scoping.md` §1.7 — full substantive resolution + symptom + tension analysis (this Decision distils §1.7 into a Decision register entry; §1.7 is preserved as the historical analysis)
- `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — IoObserver callback contract; the registration API now resides in `cranelisp-intrinsics` post-split
- `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md` — backend's substitution-table responsibility becomes explicit at the per-symbol JIT site
- `design/arch/principles.md` — Principle 1 (decoupling), Principle 7 (no duplicate addressable forms) cited as rationale
- `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` — implementation tracker; coordinates with FIXME 0103 (trace/io_trace relocation)
- `design/arch/legacy/decisions/` — Decisions 0014, 0015 NOT present (deleted in commit `754d525` per "rely on git for history"); historical bodies recoverable via `git show 754d525^:design/arch/decisions/0014-*.md` and similarly for 0015. This Decision is the formal replacement direction.

## Sequencing

Largest single migration scheduled in the architecture. Touches workspace structure, two BCs, three Decisions (this one + retracts 14 + reframes 15), multiple crates, and stdlib. Suggested as a Sprint-65+ wave gated on this Decision's acceptance — too big to bundle alongside facade-adoption work in S65's current scope.

Decision 40's IoObserver API can land in `cranelisp-runtime` first (S65 scope) and migrate to `cranelisp-intrinsics` when this Decision's wave lands; no gating dependency between the two.
