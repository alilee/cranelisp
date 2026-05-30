# Sprint 72 Wave 3a — Phase B design plan

This plan is executable by `/dev typecheck` in Wave 3b. It scopes (1) activating
`ModuleEntry::IntrinsicType`, (2) cleaning the `fqtn_for_bare_type_name`
hard-coded fallback parallel to S67's `trait_home_for` cleanup, (2b) deleting
the Tier 2 universe walk in `known_type_names_in_module` and replacing it with
on-demand FQ resolution, (3) typecheck-side prep for FIXME 0033 (MonoDefn
redundant side maps), (4) the 5-lens facade audit, (5) renaming the per-kind
resolution helpers to a uniform `resolve_*` Result-returning family with a
`ResolveError` enum, and (7) closure check on FIXMEs 0173 / 0172 / 0098.

**Cross-cutting note**: Parts 2, 2b, and 5 are three angles on the same
refactor and must land as one coherent change-set (see "Cross-cutting:
Parts 2 + 2b + 5 compose" below). Parts 1, 3, and 4 land independently.

The plan is grounded in Principle 17 (module locality), Principle 7 (single
source of truth), Decision 0048 (primitives self-owned), and the orthogonal
provenance × kind model the user authorized 2026-05-29.

---

## Part 1 — IntrinsicType activation

### 1.1 Final shape of the variant (verified against source)

`crates/cranelisp-types/src/module.rs:886` already carries the dormant variant:

```rust
IntrinsicType {
    ty: Type,                  // Type::Int, Type::Bool, Type::Float, Type::String, ...
    visibility: Visibility,
}
```

The `fq` and `seq` fields the user brief speculated about are **not** present.
The `fq` identity is keyed in the surrounding `SymbolTable` (per-module map);
the `seq` is owned by `ModuleEntry`-uniform external bookkeeping. No source
shape change is required — the variant is as-shipped.

**Disposition**: hold the variant shape as-is. No further `cranelisp-types`
edit needed — `/dev typecheck` proceeds by populating, reading, and matching on
this existing variant.

### 1.2 Registration — where, by whom

Two options were considered:

| Option | Description |
|---|---|
| A | `cranelisp-primitives::PRIMITIVES_TABLE` (Decision 0048) extends with `IntrinsicType` entries for `Int`/`Float`/`Bool`/`String`/`Vec`/`IO`/`Trace`/`TestResult`; typecheck's `register_builtin_type_names` becomes a no-op or deletes outright. |
| B | `register_builtin_type_names` (`builtins.rs:165-197`) continues to seed the primitives module, but writes `ModuleEntry::IntrinsicType { ty: Type::Int, visibility: Public }` instead of `ModuleEntry::TypeDef { info: empty-constructors TypeDefInfo, ... }`. |

**Chosen: Option B** for Phase B, with Option A as the follow-up that closes
FIXME 0239.

Rationale: Option A demands a cross-crate Decision (does `cranelisp-primitives`
seed types, or only functions?) that Phase B is not authorized to take.
FIXME 0239 (`/arch`-targeted) holds the architectural question; Phase B uses
Option B as the immediate fix, and 0239's resolution later migrates seeding to
`cranelisp-primitives` if `/arch` so directs. Option B preserves the
session-init shape that exists today and keeps the test fixture
(`seed_test_primitives`) in step.

### 1.3 Sexp is a TypeDef, not IntrinsicType

Sexp is bundled-with-language (primitives provenance) but ADT-shaped — it has
constructors (`SCons`/`SNil` on `SList`; `SexpInt`/`SexpFloat`/`SexpBool`/
`SexpStr`/`SexpSym`/`SexpList`/`SexpBracket` on `Sexp`) and per-field metadata.
The kind/shape dimension dictates `TypeDef`. The provenance dimension dictates
that it lives in module `macros` (not `primitives`). The two dimensions
compose: `macros/Sexp` is `(provenance: macros, kind: TypeDef)`; `primitives/
Int` is `(provenance: primitives, kind: IntrinsicType)`; `user/MyType` is
`(provenance: user, kind: TypeDef)`.

**Action**: `register_macros_module` (`builtins.rs:224`) continues registering
Sexp/SList as `TypeDef`. The change in Part 1.2 is scoped to the five intrinsic
scalars (`Int`, `Bool`, `Float`, `String`, `Vec`). `IO`, `Trace`, `TestResult`
are ADT-shaped (constructors) — they stay `TypeDef`.

Reconciled list of intrinsics for `IntrinsicType` registration:

- `Int` → `Type::Int`
- `Bool` → `Type::Bool`
- `Float` → `Type::Float`
- `String` → `Type::String`
- `Vec` — special case (parameterized). The current source registers it as a
  zero-constructor `TypeDef` with empty `type_params`, which is already a
  smell. Recommended: keep `Vec` as `TypeDef` for Phase B (no `Type::Vec`
  variant exists — vec is encoded via `Type::ADT(primitives/Vec, [elem])`),
  and file a follow-up FIXME if a unified treatment is wanted.

So Phase B's `IntrinsicType` entries are the **four scalar primitives** only:
`Int`, `Bool`, `Float`, `String`.

### 1.4 Consumer-site changes

The dispatch sites that today branch on "is this a builtin scalar?" become
"match on `ModuleEntry::TypeDef | ModuleEntry::IntrinsicType`":

1. **`resolve.rs:62-91` (`resolve_named`)** — drop the hard-coded
   `match name.name.as_ref() { "Int" => Type::Int, ... }` arm. Extend
   `KnownTypes` to optionally carry a `Type::Int`-style direct payload, OR
   (simpler) extend `known_type_names_in_module` (Part 1.5) to insert intrinsic
   entries keyed by their bare name + FQ name alongside `TypeDef` entries.

2. **`checker.rs:672-683` (`fqtn_for_bare_type_name`)** — drop the hard-coded
   `match type_name.as_ref() { "Int" | "Bool" | ... => primitives, _ => current }`.
   See Part 2 for the cleanup design.

3. **`traits.rs:619, 632, 794, 1097` (impl machinery)** — when constructing
   `concrete_self: Type::ADT(target_fqtn, ...)` for an impl on an intrinsic
   type, the typing rule must produce the intrinsic's `Type::Int` (etc.)
   directly rather than `Type::ADT(primitives/Int, [])`. This is where the
   bridge happens. Dispatch pattern:
   ```rust
   let concrete_self = match probe_entry(target_fqtn) {
       Some(ModuleEntry::IntrinsicType { ty, .. }) => ty.clone(),
       Some(ModuleEntry::TypeDef { .. }) => Type::ADT(target_fqtn, resolved_type_args),
       _ => /* type error: unknown impl target */,
   };
   ```

4. **`adt.rs` and `infer.rs::instantiate_ctor` (`infer.rs:134`)** — same
   dispatch when a constructor's owning type is intrinsic (it isn't today —
   intrinsics have no constructors — so this is a defensive arm: return type
   error "intrinsic type has no constructors" if reached).

5. **`builtins.rs:1057-1298` (`seed_test_primitives`)** — adopt the same
   `IntrinsicType` shape so the 26 failing unit tests get a fixture whose
   shape matches production. The Wave 3b acceptance is these tests flipping
   green. (FIXME 0239 longer-term remediation does not block this.)

### 1.5 `known_type_names_in_module` extension

`checker.rs:1890-1942` currently walks `ModuleEntry::TypeDef` only. Extend the
walk to also collect `ModuleEntry::IntrinsicType` entries:

```rust
for entry in &local_entries {
    match self.resolve_to_terminal_entry_owned(entry, 0) {
        Some(ModuleEntry::TypeDef { info, .. }) => {
            result.insert(info.name.name.clone(), (info.name.clone(), info.type_params.len()));
        }
        Some(ModuleEntry::IntrinsicType { .. }) => {
            // Use the SymbolTable key as the FQ identity; arity is 0 for all
            // current intrinsics (Int/Bool/Float/String).
            // The terminal entry's parent module + entry name gives the FQ;
            // recover via the caller-provided context or extend
            // resolve_to_terminal_entry_owned to surface (entry, home).
        }
        _ => {}
    }
}
```

The FQ identity recovery is the only mechanical complication — the entry
itself doesn't store FQ; the SymbolTable key does. Three solutions:

- (a) Extend `resolve_to_terminal_entry_owned` to return `(ModuleEntry, FQTypeName)`.
- (b) Walk via `for_each_in_module` with the home path threaded in.
- (c) Add an `fq()` helper that takes the SymbolTable key + module path.

Recommended: (b) — the home path is already in scope during the local walk.
For the universe-scoped Tier 2 pass (the second loop at L1930), the `home_path`
is `module_entry.key()`; extend the inner `match` to handle `IntrinsicType`
identically.

The downstream consumer `resolve_named` then needs no special case — the
`known_types` map carries `(fqtn, 0)` for each intrinsic, and the match falls
through to the existing `Type::ADT(fqtn, vec![])` arm — except that the
typing rule should produce `Type::Int` not `Type::ADT(primitives/Int, [])`.

This is the core question: **does `resolve_named` return `Type::Int` or
`Type::ADT(primitives/Int, vec![])` for an intrinsic?** They must unify, but
the existing source pervasively uses `Type::Int`. To minimize blast radius:

**Decision**: `resolve_named` continues to return `Type::Int` etc. for
intrinsics. The dispatch is on the entry kind:

```rust
fn resolve_named(name, known_types, span) -> Result<Type, _> {
    // ...
    if let Some((fqtn, arity)) = known_types.get(&name.name) {
        // If the entry is an IntrinsicType, return its Type directly.
        // Smuggle this by extending KnownTypes:
        //   pub type KnownTypes = HashMap<TypeName, KnownTypeKind>;
        //   pub enum KnownTypeKind {
        //       Adt { fqtn: FQTypeName, arity: usize },
        //       Intrinsic { ty: Type, fqtn: FQTypeName },
        //   }
        // ...
    }
}
```

Wave 3b implements `KnownTypeKind` (one widening of the existing `KnownTypes`
shape — backward-compat by accessor) and dispatches in `resolve_named` and
`resolve_applied`.

### 1.6 Unification bridge

After Part 1.5, the bridge between `Type::Int` and `Type::ADT(primitives/Int,
[])` should not be required because:

- `IntrinsicType` registration yields `Type::Int` everywhere `Int` is named.
- ADT-shaped types yield `Type::ADT(fqtn, args)`.

There is no callsite (post-Phase-B) where the two would meet. If the 26
failing tests reveal a callsite that still mints `Type::ADT(primitives/Int,
[])` (e.g., the impl path before the Part 1.4(3) fix), the dispatch at the
mint site is the fix, not a bridge in `unify`.

### 1.7 Listing of all consumer sites distinguishing "builtin vs user type"

| Site | File | Today | Post-Phase-B |
|---|---|---|---|
| `resolve_named` hardcoded match | `resolve.rs:72-80` | `match name.name.as_ref()` | dispatch via `KnownTypeKind` |
| `fqtn_for_bare_type_name` hardcoded match | `checker.rs:677-682` | `match type_name.as_ref()` | delete; route via symbol table |
| Impl machinery `concrete_self` build | `traits.rs:619-636, 794, 1097` | `Type::ADT(target_fqtn, args)` unconditionally | dispatch on entry kind |
| `seed_test_primitives` | `builtins.rs:1057-1298` | seeds `TypeDef` | seeds `IntrinsicType` for scalars |
| `register_builtin_type_names` | `builtins.rs:165-197` | seeds `TypeDef` | seeds `IntrinsicType` for scalars |
| `known_type_names_in_module` Tier 1 | `checker.rs:1907-1916` | walks `TypeDef` only | walks `TypeDef | IntrinsicType` |
| `known_type_names_in_module` Tier 2 | `checker.rs:1930-1939` | walks `TypeDef` only | walks `TypeDef | IntrinsicType` |

---

## Part 2 — `fqtn_for_bare_type_name` cleanup

### 2.1 Current shape (`checker.rs:670-683`)

```rust
pub(crate) fn fqtn_for_bare_type_name(
    &self,
    state: &CheckState,
    type_name: &TypeName,
) -> cranelisp_types::FQTypeName {
    if let Some(info) = self.lookup_type_def_with_state(state, type_name) {
        return info.name.clone();
    }
    // Primitive types
    let module = match type_name.as_ref() {
        "Int" | "Bool" | "Float" | "String" | "Vec" | "IO" | "Trace" | "TestResult" =>
            ModuleFullPath::from("primitives"),
        _ => state.current_module.clone(),
    };
    cranelisp_types::FQTypeName::new(module, type_name.clone())
}
```

Two violations of Principle 17:

1. The hard-coded list silently injects `primitives/<name>` FQs regardless of
   whether the bare name resolved through `state.current_module`'s import
   bindings. A user-defined type called `Vec` in their own module is
   misresolved to `primitives/Vec`.

2. The non-primitive fallback (`_ => state.current_module.clone()`) produces
   a `<current>/<name>` FQ even when the name has no entry in that module —
   masking resolution gaps.

### 2.2 Post-S67 precedent (`trait_home_for`, `checker.rs:697-702`)

```rust
pub(crate) fn trait_home_for(&self, state: &CheckState, trait_name: &str)
    -> Option<ModuleFullPath>
{
    match self.resolve_terminal_entry_and_home(&state.current_module, trait_name) {
        Some((ModuleEntry::TraitDecl { .. }, home)) => Some(home),
        _ => None,
    }
}
```

Caller validates existence first; the helper returns `Option`; no fallback.

### 2.3 Post-cleanup shape

```rust
pub(crate) fn fqtn_for_bare_type_name(
    &self,
    state: &CheckState,
    type_name: &TypeName,
) -> Option<cranelisp_types::FQTypeName> {
    match self.resolve_terminal_entry_and_home(&state.current_module, type_name.as_ref()) {
        Some((ModuleEntry::TypeDef { info, .. }, _home)) => Some(info.name.clone()),
        Some((ModuleEntry::IntrinsicType { .. }, home)) => {
            // Intrinsic's FQ is (home, type_name) — home is the synthetic
            // module that owns the entry (typically `primitives`).
            Some(cranelisp_types::FQTypeName::new(home, type_name.clone()))
        }
        _ => None,
    }
}
```

### 2.4 Callers and their adaptation

| Caller | File:Line | Today | Post-cleanup |
|---|---|---|---|
| Impl-write retarget | `traits.rs:439` | unconditional FQ | validate `Option`; on `None` emit type error "unknown impl target" |
| Polymorphic impl arg lift | `traits.rs:632` | unconditional FQ | same |
| Body-check FQ lift | `traits.rs:619` | unconditional FQ | same |
| HKT impl-arg lift | `traits.rs:794` | unconditional FQ | same |
| Body-check trait-method-target | `traits.rs:1097` | unconditional FQ | same |

The error-emission layer one step up (the typing rule that contains the call)
already participates in `CheckError::TypeError { message, location }`; the
plumbing exists. The five callsites become `let fqtn = self.fqtn_for_bare_type_name(state, name).ok_or_else(|| /* TypeError */)?;`.

Wave 3b acceptance: the 26 failing tests flip green; no test that exercised
the hardcoded fallback's silent-correct path regresses (any such test was
relying on a workaround, not a contract — fix the test).

---

## Part 2b — Delete the Tier 2 universe walk; replace with on-demand FQ resolution

### 2b.1 Current Tier 2 shape (`checker.rs:1918-1939`)

The `known_type_names_in_module` walk has two tiers. Tier 1 is the
import-scoped, principled walk over `module_path`'s symbol table. Tier 2 is
an exhaustive iteration over **every loaded module** that injects an FQ-keyed
entry (`module/name → (fqtn, arity)`) into the result map for every `TypeDef`
in the universe:

```rust
// Tier 2 (universe-scoped, FQ keys): every type defined in any loaded
// module is also addressable by its fully-qualified name (`module/name`).
// FQ refs are explicit module specifications by the source author — NOT
// a fallback or graph walk, so Principle 17's "no fallback" does not
// apply. The bare-name keys above remain import-scoped; the FQ keys are
// a parallel direct-addressing surface.
for module_entry in self.modules.iter() {
    let home_path = module_entry.key();
    for (_name, entry) in module_entry.value().all_symbols() {
        if let ModuleEntry::TypeDef { info, .. } = &entry {
            let fq_key =
                cranelisp_types::TypeName::from(format!("{home_path}/{}", info.name.name));
            result.insert(fq_key, (info.name.clone(), info.type_params.len()));
        }
    }
}
```

The Tier 2 walk supports FQ references like `macros/SList` without
requiring `(import [macros [SList]])`. Cost: O(modules × entries-per-module)
**per inference operation that calls `known_type_names_*`**.

### 2b.2 Hot-path callers (verified)

The `known_type_names*` family is called from these sites:

| Caller | File:Line | Context |
|---|---|---|
| `compile_defn_body` (ADT path) | `adt.rs:219` | per-defn typecheck — runs the full walk per `Defn` |
| `instantiate_named_type` | `infer.rs:322` | per-`TypeExpr::Named` resolution during inference |
| `check_type_annotation` | `infer.rs:975` | per-annotation site during inference |
| `program.rs` body-check | `program.rs:2240` | per-form path in `check_program`'s typing loop |
| `bulk_resolve_constructors` | `adt.rs:1073` | not strictly hot — runs once per program-check |
| REPL public accessor | `checker.rs:2486` | `TypeChecker::known_type_names()` — `/list` and friends |

The four hot-path callers (adt.rs:219, infer.rs:322, infer.rs:975,
program.rs:2240) each construct the full universe-scoped `KnownTypes`
map every time they are called. For a module-graph with M modules and
~T types per module, each call materialises ~M×T FQ-keyed entries.

### 2b.3 Proposed delete

Delete the Tier 2 loop entirely from `known_type_names_in_module`. The
map shrinks to Tier 1 only: the import-scoped bare-name index.

Push FQ resolution **down into the resolver** (`resolve.rs`):

```rust
// resolve.rs — new entry point for resolve_named / resolve_applied
fn resolve_named(
    name: &TypeRef,                       // carries module: Option<ModuleFullPath>
    known_types: &KnownTypes,
    tc: &TypeChecker,                     // OR a thin resolver trait — see 2b.5
    span: Span,
) -> Result<Type, ResolveError> {
    // Intrinsic short-circuit retained from Part 1.5
    if name.module.is_none() {
        match name.name.as_ref() {
            "Int"    => return Ok(Type::Int),
            "Bool"   => return Ok(Type::Bool),
            "Float"  => return Ok(Type::Float),
            "String" => return Ok(Type::String),
            _ => {}
        }
    }

    // FQ path: name carries module — resolve directly via the symbol table.
    if let Some(module) = &name.module {
        return match tc.resolve_terminal_entry_and_home(module, name.name.as_ref()) {
            Some((ModuleEntry::TypeDef { info, .. }, _home)) =>
                Ok(Type::ADT(info.name.clone(), vec![])),
            Some((ModuleEntry::IntrinsicType { ty, .. }, _home)) =>
                Ok(ty.clone()),
            Some(_) => Err(ResolveError::TypeNotFound {
                name: name.name.clone(),
                from_module: tc.current_module(),
                span,
            }),
            None => Err(ResolveError::QualifiedModuleUnknown {
                module: module.clone(),
                name: Symbol::from(name.name.as_ref()),
                span,
            }),
        };
    }

    // Bare path: Tier 1 lookup against import-scoped known_types.
    if let Some((fqtn, _arity)) = known_types.get(&name.name) {
        return Ok(Type::ADT(fqtn.clone(), vec![]));
    }

    Err(ResolveError::TypeNotFound {
        name: name.name.clone(),
        from_module: tc.current_module(),
        span,
    })
}
```

Symmetric change for `resolve_applied` — the FQ branch calls
`resolve_terminal_entry_and_home` directly, the bare branch consults
`known_types`. Both branches share arity validation against the looked-up
`TypeDef.type_params`.

### 2b.4 Per-call cost

- Today (Tier 2): O(M × T) per `known_type_names_*` call. With M ~50
  modules and T ~10 types per module, each call materialises ~500 map
  insertions. Inference invokes this **per type-expr resolution** at
  hot sites — total cost compounds across the inference pass.
- Post-delete: bare lookup is O(1) hash hit against Tier 1's index; FQ
  lookup is O(1) hash hit against the named module's `SymbolTable` (the
  existing `probe_module_entry_owned` primitive). No per-call universe
  materialisation.

### 2b.5 Resolver-trait shape question

`resolve_named` / `resolve_applied` are free functions in `resolve.rs`
today; they cannot call `TypeChecker::resolve_terminal_entry_and_home`
without a handle. Two options:

| Option | Description |
|---|---|
| (i) Pass `&TypeChecker` directly | Simplest; `resolve.rs` already holds a `&KnownTypes` parameter. Adds a `&TypeChecker<C, L>` parameter. |
| (ii) Define a `Resolver` trait | A 1-method trait `Resolver { fn resolve_terminal_entry_and_home(...) -> Option<(ModuleEntry, ModuleFullPath)> }` implemented by `TypeChecker`. Keeps `resolve.rs` decoupled from `TypeChecker`'s generic parameters. |

**Recommended: (ii)** — `resolve.rs` is already type-parameter-free; the
trait keeps it that way and avoids forcing `<C, L>` through every
resolver call site. The trait can be defined in `resolve.rs` and
implemented for `TypeChecker<C, L>` in `checker.rs`. One method, narrow
surface, satisfies Principle 2.

### 2b.6 Edge cases

| Edge | Today's Tier 2 behaviour | Post-delete behaviour |
|---|---|---|
| `module/Name` where `module` is loaded & has `Name` | Hit | Hit via `resolve_terminal_entry_and_home` |
| `module/Name` where `module` is loaded but `Name` absent | Miss (returns `TypeNotFound`-equivalent) | `ResolveError::TypeNotFound { from_module: <current> }` |
| `module/Name` where `module` is not loaded | Miss (Tier 2 silently skips it) | `ResolveError::QualifiedModuleUnknown` — explicit error |
| `Name` (bare) where `Name` is import-reachable from current module | Hit (Tier 1 or Tier 2 — both inserted) | Hit (Tier 1 only) |
| `Name` (bare) where `Name` is defined in some loaded module but NOT imported into current | **Today: hit via Tier 2** (FQ key not bare key — but Tier 2 also injects bare-name shadowing if name happens to match an FQ key prefix). Existing tests rely on this only when the call site actually uses an FQ ref. | Post-delete: not hit. Bare names resolve only via Tier 1 (import-scoped). This is the principled outcome — bare references through the universe were never spec-correct. |

The last row is the only behavioural narrowing — and it aligns with
Principle 17 ("bare-name lookups are import-scoped; cross-module
addressing requires FQ"). Any test or call site that depended on the
Tier 2 bare-name leak is exposing a latent ambiguity (which module's
`Foo` did the user mean?) and should be rewritten to use an explicit
FQ or `(import ...)`.

### 2b.7 Aligned with Principle 17 and post-S67 precedent

`trait_home_for` (S67 cleanup, `checker.rs:697-702`) is the structural
precedent: caller validates existence; helper calls
`resolve_terminal_entry_and_home` directly; no per-call universe
materialisation. Part 2b extends the same shape to type resolution.

---

## Part 3 — FIXME 0033 typecheck-side prep (MonoDefn redundant side maps)

### 3.1 Current state (confirmed)

`MonoDefn` at `crates/cranelisp-types/src/check.rs:134-140`:

```rust
pub struct MonoDefn {
    pub defn: Defn,
    pub resolutions: MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
}
```

Populated at `traits.rs:1427-1431`:

```rust
let mono_defn = MonoDefn {
    defn: mono_defn_ast,
    resolutions,
    expr_types: mono_expr_types,
};
```

Read by `cranelisp-backend` only:
- `crates/cranelisp-backend/src/lib.rs:1266-1270` — `merged.extend(mono.resolutions.clone())`; `if mono.expr_types.is_empty() { &check.expr_types } else { &mono.expr_types }`.
- And by `register_mono_entry` at `traits.rs:1439-1459` which calls
  `annotate_defn_from_maps` BEFORE building the `MonoDefn` — so `mono_defn_ast`
  is already annotated in-place. The side maps on `MonoDefn` then duplicate
  what's on `Def.ast`.

### 3.2 Canonical homes (per S55 Phase 1)

- `Expr.inferred_type: Option<Type>` — every typed expr node carries its type.
- `Expr::Apply.resolved_call: Option<ResolvedCall>` — every call carries its
  resolution.

The `mono_defn_ast` is annotated by `annotate_defn_from_maps` at L1420 just
before `MonoDefn` construction. The side maps on `MonoDefn` are therefore
**already redundant at the point of construction**.

### 3.3 Migration design

**Step A (Phase B, typecheck-side prep — Wave 3b)**:

1. Stop populating `mono.resolutions` and `mono.expr_types` at `traits.rs:1427-1431`. Replace with `MethodResolutions::default()` / `HashMap::new()`.

2. Verify the `register_mono_entry` annotation flow at L1420 stays — it's the
   canonical AST-annotation path, and backend reads `Def.ast` for the mono.

3. The struct shape stays unchanged in `cranelisp-types`; only the population
   pattern changes. This is non-breaking at the cross-crate boundary —
   backend still reads the (now-empty) fields and falls through to its
   `check.expr_types` / `check.method_resolutions` overlay.

4. Backend's downstream behavior is unchanged because the `&check` overlay
   covers what the per-mono maps used to: the AST annotation pass on
   `Def.ast` is what the side maps were caching anyway. The empty per-mono
   fields make the `mono.expr_types.is_empty()` branch (`lib.rs:1267`) take
   the `&check.expr_types` path uniformly.

5. **No test changes mandated by this step.** The 26 failing tests are
   IntrinsicType-related, not MonoDefn-related. The backend tests that
   exercise mono dispatch continue to work because the typed AST carries the
   data the side maps used to.

**Step B (out of Phase B scope — Wave 4+ backend triad)**:

Backend reads from `Defn.body`'s annotated `Expr.inferred_type` /
`Expr::Apply.resolved_call` directly. The side-map overlay
(`enrich_defn_from_side_maps` at backend `lib.rs:1194`, 1254, 1260, 3415, 4023)
deletes. Then `MonoDefn` shrinks to a `Defn` newtype, removing the redundant
fields from `cranelisp-types`.

Step B is a backend-side change; Phase B prepares the ground by ensuring the
typecheck side already produces fully-annotated `Defn.body` AST and stops
populating the maps that backend would otherwise stale-read.

### 3.4 Why typecheck-side Step A is safe in isolation

Backend's overlay (`mono.expr_types.is_empty() ? &check.expr_types :
&mono.expr_types`) is robust to an empty per-mono map: it falls through to the
program-level `check.expr_types` and `check.method_resolutions`. The
annotated `Defn.body` carries the precise information already; the program-
level overlay is the secondary cache the backend currently uses for
non-annotated paths. Step A removes the per-mono cache; the cluster-level
overlay covers.

---

## Part 4 — 5-lens audit of `facades/typecheck.md` vs post-Wave-2 source

The audit grounds disposition decisions in Decisions / Principles / FIXMEs per
the `feedback_audit_per_item_analysis` template. Default: source-moves
(facade is target-stating, per `feedback_hold_to_facade_default`).

### A1 — `check_forms` signature

**Facade expects** (L15-21): `check_forms(parsed, ctx: &mut ClusterContext, symbol_tables: &SymbolTables, module_aliases: &ModuleAliases) -> Result<(), CheckError>`.

**Source does** (`public-api.txt:152`): `check_forms(parsed, ctx, symbol_tables) -> Result<(), CheckError>` — **no `module_aliases` parameter**. The `state.module_aliases: HashMap<Symbol, ModuleFullPath>` is on `CheckState` (`checker.rs:75`).

**Design intent grounding**: Decision 44 third amendment + facade §"Cluster check scaffolding" both specify the four-parameter shape. `bounded-contexts.md` §7 mandates session-level `ModuleAliases` table.

**Difference**: 1 missing parameter; aliases are state-local instead of session-level.

**Disposition**: **source moves** — Wave 3b adds `module_aliases: &ModuleAliases` parameter and migrates the per-call alias store onto the session-level table. Hold to facade per `feedback_hold_to_facade_default`. ~1-2 day effort.

### A2 — `TypeCheckEnv` narrowing (S67 PIF row 21)

**Facade expects** (L151-158): exactly two public methods — `new`, `next_type_id`.

**Source does** (`public-api.txt:137-143`): 6 public methods (`ensure_module_exists`, `new`, `next_type_id`, `register_exports`, `register_imports`, `restore`, `snapshot`).

**Design intent grounding**: facade §"TypeCheckEnv target shape" + S67 PIF row 21 + FIXME 0172 deferred-with-named-residue (depends on FIXME 0187 `int`-side migration to release `pub` → `pub(crate)`).

**Difference**: 4 methods over budget (`ensure_module_exists`, `register_exports`, `register_imports`, `restore`, `snapshot`).

**Disposition**: **partial source-move** — `register_imports`/`register_exports` keep facade-side as **free functions** with `module_aliases` parameter; the method-form delegates retire. `snapshot`/`restore`/`ensure_module_exists` retain `pub` until FIXME 0187 clears `int`-side consumers, then narrow to `pub(crate)`. Note in plan: this is paced by FIXME 0187, not Phase B. ~0.5 day for the imports/exports narrowing if combined with Part 1's free-fn module_aliases addition.

### A3 — Invariant 10 module-locality

**Facade expects** (L372-406): four principled shapes; no unbounded scans.

**Source does**: `known_type_names_in_module` Tier 2 (`checker.rs:1930-1939`) iterates `self.modules.iter()` — this is the universe scan that invariant 10 forbids for short-name resolution. The rustdoc at L1918 frames it as FQ-key parallel-addressing, but the structural scan IS the violation pattern.

**Design intent grounding**: Principle 17, Decision 0045, FIXME 0172. The Tier 2 walk is the same "build FQ index by iterating modules" smell that Principle 17 names.

**Difference**: Tier 2 universe scan present; not flagged by Principle 17's per-shape probe list.

**Disposition**: **note and defer** — the Tier 2 walk is a per-call ad-hoc index, not a stored short-name fallback chain. The facade's invariant text targets short-name lookup pathways, which Tier 2 doesn't serve (it provides FQ-key addressing as Principle 17 §"FQ refs are explicit module specifications"). However, the universe iteration cost grows linearly with modules — file a follow-up FIXME if perf surfaces. **No Phase B change**; ~0 day.

### A4 — `register_imports`/`register_exports` free-fn shape (FIXME 0192)

**Facade expects** (L226-246): five-parameter shape including `&ModuleAliases`.

**Source does** (`public-api.txt:156-157`): four-parameter shape — no `module_aliases`.

**Design intent grounding**: FIXME 0192 + facade §"Module-lifecycle free functions" + `bounded-contexts.md` §7 "Module aliases live at session level".

**Difference**: 1 parameter missing; aliases stored on `CheckState` instead of session.

**Disposition**: **source-moves**, combined with A1 — the same session-level `ModuleAliases` table threading change. ~1-2 day combined.

### A5 — Trace hook surface

**Facade expects** (L181-217): `trace::install_symbol_table_ensure_hook`, `emit_symbol_table_ensure`, `SymbolTableEnsureHook`, `SymbolTableEnsureOutcome` re-exported at crate root.

**Source does** (`public-api.txt:44-50, 153-154, 158`): all five items present at crate root.

**Design intent grounding**: Decision 40 + FIXME 0103.

**Difference**: none.

**Disposition**: **no change**. Audit-side verification only: confirm `cranelisp-int` installs the hook at startup (out of Phase B scope; `/int` confirms).

### A6 — Two legacy crate-root re-exports

**Facade expects** (L325-326): `CranelispError`/`TopLevel` re-exports flagged as housekeeping — removal once external sites are confirmed clean.

**Source does** (`public-api.txt:2-3`): both re-exports present.

**Design intent grounding**: Principle 15 — multi-consumer types live in `cranelisp-types`; re-exports are convenience, not endorsement.

**Difference**: re-exports present per facade housekeeping note.

**Disposition**: **no Phase B change** — track in Wave 4 housekeeping pass. Net cost: a `cargo public-api` baseline change plus updating any `cranelisp_typecheck::CranelispError` import sites to `cranelisp_types::CranelispError`. ~0.5 day in a future sprint.

### A7 — `SymbolTableRead`/`SymbolTableMut` single-pair invariant

**Facade expects** (L92-127, L143): one pair only; `TypeCheckEnv::current_symbol_table[_mut]` returns the same types.

**Source does** (`public-api.txt:65-92`): `SymbolTableRead`, `SymbolTableMut` types defined; deref-target impls present. **`TypeCheckEnv::current_symbol_table[_mut]` accessors NOT present in public-api.txt baseline** — meaning either the env accessors are `pub(crate)` (not crossing the facade), OR they don't yet exist on `TypeCheckEnv`.

**Design intent grounding**: Wave 2 /review I-2; user arbitration 2026-05-29; facade §"Single-pair invariant".

**Difference**: env-surface accessors are not at the public boundary as the facade text mandates ("returned by BOTH `ClusterContext::current_symbol_table()` AND `TypeCheckEnv::current_symbol_table()`").

**Disposition**: **source-moves** — expose `TypeCheckEnv::current_symbol_table[_mut]` at the public surface returning `SymbolTableRead`/`SymbolTableMut`. ~0.5 day. Required for single-pair-invariant compliance per Wave 2 outcome.

### A8 — `ConstrADT` typing rule

**Facade expects** (L412-423): typing rule + ctor scheme inference + `constructor_to_type` retirement.

**Source does**: Wave 1 implemented; `infer.rs::instantiate_ctor` (L134) is the shared helper; `constructor_to_type` reverse-index retired per `DefKind::Constructor`.

**Design intent grounding**: facade text + S70 Trigger 2.

**Difference**: none.

**Disposition**: **no change**. Audit-side note: cross-link in source rustdoc on `infer.rs::instantiate_ctor` to facade §"Typing rule for Expr::ConstrADT".

### A9 — `instantiate_ctor` helper

**Facade expects**: no specific mention; implied by §"Typing rule".

**Source does**: `infer.rs:134` defines `pub(crate) fn instantiate_ctor`; called at L97 and L778.

**Disposition**: **no change**. Internal helper; not a public-surface item.

### A10 — Configuration-walk (5th lens) — type identifiers from facade text

Walked: `Int`, `Bool`, `Float`, `String`, `Vec`, `IO`, `Trace`, `TestResult`, `Sexp`, `SList`, `Option` (all named in facade or `bounded-contexts.md`).

**Found in source**:
- `Int`, `Bool`, `Float`, `String` — `Type::Int` etc.; planned `IntrinsicType` registration in Part 1.
- `Vec`, `IO`, `Trace`, `TestResult`, `Sexp`, `SList`, `Option` — all registered as `TypeDef` per `builtins.rs` (verified).

**Difference**: `Int`/`Bool`/`Float`/`String` are intrinsic-shaped per design but registered as `TypeDef` per source — Part 1 closes the gap.

**Disposition**: subsumed in Part 1.

---

## Part 5 — Naming unification + `ResolveError` + Result return

The per-kind ad-hoc lookup family in `checker.rs` (one shape per kind,
each with three variants — default / module-rooted / state-rooted) is
replaced with a uniform `resolve_*` family returning
`Result<_, ResolveError>`. Hard-coded fallbacks (Part 2) and the
universe walk (Part 2b) disappear in the same change-set; what's left
is the narrow public surface that the rest of the typechecker consumes.

### 5.1 Rename table

| Current name | Proposed name | Return type | Site count |
|---|---|---|---|
| `trait_home_for(state, name) -> Option<ModuleFullPath>` (checker.rs:697) | `resolve_trait(state, name, span) -> Result<ModuleFullPath, ResolveError>` | Result | 2 call sites (`traits.rs:430`, `traits.rs:1086`) |
| `fqtn_for_bare_type_name(state, name) -> FQTypeName` (checker.rs:672) | `resolve_type(state, name, span) -> Result<FQTypeName, ResolveError>` | Result | 5 call sites (`traits.rs:439, 619, 632, 794, 1097`) |
| `lookup_constructor_type` family (3 variants, checker.rs:458, 464, 486) | `resolve_constructor(state, name, span) -> Result<(FQTypeName, ConstructorIdx), ResolveError>` | Result | 4 production sites (`infer.rs:818, 821`, `checker.rs:510` (internal), `checker.rs:2360` public) + ~7 test-only sites |

Total rename surface: **~11 production call sites** that gain richer
errors and `?` propagation. Plus test fixtures that update the
constructor signature (the new tuple return surfaces `ConstructorIdx`
which today is looked up separately).

The `ConstructorIdx` augmentation: today's `lookup_constructor_type`
returns `Option<TypeName>` and callers separately probe the Def or
TypeDef to find the constructor's index/scheme. The proposed
`resolve_constructor` returns both the parent type's FQ and the
ConstructorIdx in one call — collapsing the three-variant family AND
the post-lookup re-probe into one resolver. If the broader sweep is
too big for Wave 3b, the minimum is to collapse the three variants
while keeping the return type as `TypeName` only; the `ConstructorIdx`
addition can be deferred. Plan recommends the full sweep.

### 5.2 `ResolveError` enum (full)

```rust
/// Error type for resolution functions.
///
/// Each variant carries enough context to produce a user-facing message
/// without further lookups: the name being resolved, the calling module
/// (so messages can say "from <module>"), and the source span.
///
/// Grounded in Principle 17 (module locality — resolution failures are
/// scoped to the calling module's import frontier) and Principle 2
/// (narrow interfaces — one Result-shaped surface per resolution kind).
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum ResolveError {
    /// Trait name is not reachable from the calling module's import scope,
    /// nor anywhere on its chain-follow path.
    TraitNotFound {
        name: TraitName,
        from_module: ModuleFullPath,
        span: Span,
    },

    /// Type name is not reachable from the calling module's import scope.
    /// Includes the intrinsic short-names (`Int`/`Bool`/`Float`/`String`)
    /// once those land via `IntrinsicType` registration — there's no
    /// hardcoded fallback any more (per Part 2).
    TypeNotFound {
        name: TypeName,
        from_module: ModuleFullPath,
        span: Span,
    },

    /// Constructor name is not reachable, OR is reachable but is not a
    /// `DefKind::Constructor` / `TypeDef.constructor_scheme` (e.g., a
    /// regular `Def` of the same name shadows it).
    ConstructorNotFound {
        name: Symbol,
        from_module: ModuleFullPath,
        span: Span,
    },

    /// FQ reference like `module/name` where `module` doesn't exist or
    /// isn't loaded. Distinct from `*NotFound` because the failure is at
    /// module-resolution, not name-resolution. Surfaces from Part 2b's
    /// FQ resolution branch.
    QualifiedModuleUnknown {
        module: ModuleFullPath,
        name: Symbol,
        span: Span,
    },

    /// Name exists in `defining_module` but its visibility forbids access
    /// from `from_module`. Lets the user-facing message say "X is private
    /// to module Y" instead of "X not found".
    PrivateInaccessible {
        name: Symbol,
        defining_module: ModuleFullPath,
        from_module: ModuleFullPath,
        visibility_found: Visibility,
        span: Span,
    },
}

impl From<ResolveError> for CheckError {
    fn from(e: ResolveError) -> CheckError {
        // Each variant projects to CheckError::TypeError with a
        // user-facing message + location. Span on ResolveError becomes
        // ErrorLocation::from_span. Existing `?` propagation through
        // CheckError continues unchanged.
        match e {
            ResolveError::TraitNotFound { name, from_module, span } => CheckError::TypeError {
                message: format!("unknown trait `{name}` (from module `{from_module}`)"),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::TypeNotFound { name, from_module, span } => CheckError::TypeError {
                message: format!("unknown type `{name}` (from module `{from_module}`)"),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::ConstructorNotFound { name, from_module, span } => CheckError::TypeError {
                message: format!("unknown constructor `{name}` (from module `{from_module}`)"),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::QualifiedModuleUnknown { module, name, span } => CheckError::TypeError {
                message: format!("module `{module}` referenced by `{module}/{name}` is not loaded"),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::PrivateInaccessible {
                name,
                defining_module,
                from_module,
                visibility_found: _,
                span,
            } => CheckError::TypeError {
                message: format!(
                    "`{name}` is private to module `{defining_module}`; not accessible from `{from_module}`"
                ),
                location: ErrorLocation::from_span(span),
            },
        }
    }
}
```

### 5.3 Placement decision — typecheck-local

`ResolveError` is **`pub` from `cranelisp-typecheck`**, not lifted to
`cranelisp-types`.

**Rationale**:

1. **Only typecheck produces these errors.** The resolution functions
   (`resolve_trait` / `resolve_type` / `resolve_constructor`) live on
   `TypeChecker` and are called only from typecheck-internal sites.
   The errors never propagate as `ResolveError` across the crate
   boundary — they project to `CheckError` via the `From` impl above
   before `?`-bubbling reaches the public `check_forms` surface.

2. **Only typecheck consumes these errors** (in their `ResolveError`
   shape — `CheckError` consumers downstream see only the projected
   form). Frontend produces `ResolutionGap` (which IS in
   `cranelisp-types` because frontend + typecheck both originate it
   per Principle 15). No analogous cross-crate origination for
   `ResolveError`.

3. **Principle 15** ("facade types live with behavior") — types live
   in `cranelisp-types` when multiple crates produce or consume them.
   `ResolveError` fails this test: one producer (typecheck), one
   consumer that uses the typed form (typecheck), and one downstream
   consumer that uses only the projected `CheckError` (everything
   that reads `check_forms`'s `Result`).

4. **Principle 6** (complexity has a budget) — lifting to
   `cranelisp-types` would force `cranelisp-types` to import or
   re-export `Visibility`, `TraitName`, `TypeName`, `Symbol`,
   `ModuleFullPath` together in one error enum. Those are all already
   in `cranelisp-types`, so the cost is low — but the **value** is
   zero because no other crate ever holds a `ResolveError` typed
   value.

**Counter-argument considered**: if `cranelisp-backend` ever needed to
distinguish "missing trait at codegen" from "missing type at codegen",
a typed `ResolveError` returned by backend would be useful — but
backend reads through `check.method_resolutions` / `check.expr_types`
post-typecheck, not through the resolver, so this never materialises.

**Disposition**: typecheck-local `pub enum ResolveError`. Re-evaluate
**only if** a later sprint introduces a non-typecheck consumer.

### 5.4 `PrivateInaccessible` detection

The visibility check lives at the **resolver-primitive layer**, not in
the per-kind narrows. Specifically:

- The primitive `resolve_terminal_entry_and_home` is the chain-follow
  walker (`checker.rs:930`). It returns `Some((ModuleEntry, home))`
  without visibility filtering today.
- The per-kind narrows (`resolve_trait`, `resolve_type`,
  `resolve_constructor`) wrap this primitive and pattern-match on the
  `ModuleEntry` variant.

The visibility check is **the per-kind narrow's responsibility**:
after the primitive returns a terminal entry, the narrow checks
`entry.visibility()` against the calling module's reach. If the entry
is `Visibility::Private` and `home_module ≠ state.current_module` (and
is not on the calling module's accessible subtree per spec §8.7.3),
the narrow emits `ResolveError::PrivateInaccessible`. Otherwise the
narrow projects to the success variant.

Rationale for narrow-not-primitive placement:

1. The primitive serves multiple per-kind consumers; if it filtered
   visibility eagerly, the per-kind narrows would lose the ability to
   produce kind-tagged errors (the visibility-filtered miss is
   indistinguishable from a true miss).
2. Visibility checks are spec-rule-bearing (§8.7.3) — they belong at
   the rule-applying layer, not the structural walker.
3. The primitive's `Option` return stays narrow (Principle 2); the
   visibility decision rides in the wrapper.

**Implementation note**: a small helper
`visibility_accessible(home: &ModuleFullPath, from: &ModuleFullPath,
visibility: Visibility) -> bool` factored from `resolve_qualified`'s
existing visibility check (`checker.rs:963+`) is reused. No new
spec-rule introduction; just a refactor of an existing internal
helper into a shared utility.

### 5.5 Call-site impact summary

| Migration step | Sites touched | Net effect |
|---|---|---|
| Add `ResolveError` enum + `From<ResolveError> for CheckError` | 1 new module (`resolve_error.rs` or inline in `lib.rs`) | New public type |
| Introduce `resolve_trait` / `resolve_type` / `resolve_constructor` alongside old names | new code in `checker.rs` | Both surfaces coexist briefly |
| Migrate 5 `fqtn_for_bare_type_name` sites in `traits.rs` | 5 sites become `let fqtn = self.resolve_type(state, name, span)?;` | Richer error on failure; loss of silent fallback |
| Migrate 2 `trait_home_for` sites in `traits.rs` | 2 sites become `let home = self.resolve_trait(state, name, span)?;` | Same |
| Migrate ~4 production `lookup_constructor_type*` sites | 4 sites become `let (fqtn, idx) = self.resolve_constructor(state, name, span)?;` (or the narrowed `(_, TypeName)` form if `ConstructorIdx` deferred) | Same |
| Delete old `fqtn_for_bare_type_name`, `trait_home_for`, `lookup_constructor_type[_in_module/_with_state]` | checker.rs:458-491, 670-702 | Surface shrink; old names gone |
| Update test-only `lookup_constructor_type` sites | 7 test sites in `program.rs`, `adt.rs`, `builtins.rs` | Test fixture rename; semantic-preserving |

Net public-API impact (`public-api.txt` diff):
- `+ pub enum ResolveError` (or `pub(crate)` if test fixtures don't need it externally)
- `+ pub fn resolve_trait`, `+ pub fn resolve_type`, `+ pub fn resolve_constructor` on `TypeChecker`
- `- pub fn trait_home_for`, `- pub fn fqtn_for_bare_type_name`, `- pub fn lookup_constructor_type[_in_module/_with_state]` (if `pub`; many are `pub(crate)` already)

### 5.6 Facade impact

**Renames cascade to `design/arch/facades/typecheck.md` in Phase C.**
The facade's "Per-kind lookup helpers" section (or equivalent) names
the current shape `trait_home_for` / `fqtn_for_bare_type_name` /
`lookup_constructor_type`. Phase C lands the rename in the facade
authoritatively; Phase B implements + provides the spec-grounded
rationale for `/arch` to bless.

`/dev` MUST NOT edit `facades/typecheck.md` (per `/dev` boundary). The
rename pre-conditions the facade edit; once the source lands, file a
FIXME `target: /arch` to cascade the rename into the facade.

---

## Cross-cutting: Parts 2 + 2b + 5 compose as one refactor

Parts 2, 2b, and 5 are three angles on the same architectural correction:

- **Part 2** deletes the hard-coded primitive-FQ fallback in
  `fqtn_for_bare_type_name`.
- **Part 2b** deletes the Tier 2 universe walk that
  `known_type_names_in_module` performs.
- **Part 5** renames `fqtn_for_bare_type_name` to `resolve_type`,
  changes its return to `Result<FQTypeName, ResolveError>`, and
  unifies the per-kind family.

They must land together — not three independent sub-passes — because
each unblocks the next and each leaves the typechecker in a different
intermediate state:

| Land | Intermediate state |
|---|---|
| Only Part 2 (fallback delete, signature unchanged) | `Option<FQTypeName>` return — silent miss; no rich error context; callers each panic or convert ad-hoc |
| Only Part 2b (universe walk delete) | Tier 1 only — bare FQ refs (e.g., `macros/SList` without import) become "unknown type"; no on-demand FQ branch exists yet because `resolve_named` still consults only `known_types` |
| Only Part 5 (rename + Result, with old internals) | Names change but the Tier 2 universe walk continues to drive cost; the `ResolveError::QualifiedModuleUnknown` variant has no producer |

**Recommended execution order within the change-set** (for `/dev`):

1. **Introduce `ResolveError` + `From<ResolveError> for CheckError`** —
   new code, no consumer yet; backward-compat. Run `cargo nextest run
   -p cranelisp-typecheck` → green expected.

2. **Introduce `resolve_trait` / `resolve_type` / `resolve_constructor`
   alongside the old names** — copy the per-kind narrows; the new
   `resolve_type` calls `resolve_terminal_entry_and_home` directly
   (Part 5 shape + Part 2 fallback-delete combined); the old
   `fqtn_for_bare_type_name` continues to exist with its old behaviour.
   Run `cargo check -p cranelisp-typecheck` → green expected.

3. **Refactor `resolve_named` / `resolve_applied` in `resolve.rs`** to
   take the new `Resolver` trait handle (Part 2b.5 option (ii)), and
   branch on the FQ vs bare form. Tier 2 still populates `KnownTypes`;
   the resolver now has two ways to find FQ entries. Run `cargo
   nextest run -p cranelisp-typecheck` → green expected (Tier 2
   results are redundant but consistent).

4. **Migrate 11 call sites in `traits.rs` + `infer.rs`** to the
   `resolve_*` names with `?` propagation. The `From<ResolveError>
   for CheckError` handles error projection. Run `cargo nextest run
   -p cranelisp-typecheck` → green expected.

5. **Delete the Tier 2 universe walk in
   `known_type_names_in_module`**. The FQ branch in `resolve_named`
   (step 3) now covers the use case. Run `cargo nextest run -p
   cranelisp-typecheck` → green if Part 2b.6's edge analysis is
   complete; investigate any test that relied on the bare-name
   universe leak.

6. **Delete old `fqtn_for_bare_type_name`, `trait_home_for`,
   `lookup_constructor_type[_in_module/_with_state]`**. Update the
   ~7 test-only call sites. Run `cargo nextest run -p
   cranelisp-typecheck` → green expected.

Each step is independently committable + reversible. Verify green at
each step; do NOT batch.

`/dev` files FIXME `target: /arch` after landing for the
facade-side rename cascade (Phase C concern).

---

## Part 7 — FIXME closure check

### 7.1 FIXME 0173 — `CheckPass` + `ModuleCheckAccumulator` removal

Search of source surfaces:
- `pub enum CheckPass` — **not present** in lib.rs re-exports (per `public-api.txt`).
- `pub struct ModuleCheckAccumulator` — **not present**.
- `lib.rs:25-26` carries a comment "The pre-S66 `CheckPass`, `FormCheckResult`, and `ModuleCheckAccumulator` public types are [removed]" confirming intent landed.
- **However**: `crate::program::CheckPass`, `crate::program::ModuleCheckAccumulator`, `crate::program::FormCheckResult` are still referenced by `checker.rs:2439-2461` and used by `form.rs:55, 168, 184, 195, 208, 218`. These are `pub(crate)` internal scaffolding.

**Disposition**: **closeable from a public-API perspective**. Internal `pub(crate)` scaffolding remains and is permitted by Decision 44 third amendment ("Internal multi-pass scaffolding may retain a `pub(crate)` enum or two `pub(crate)` helpers if convenient"). FIXME 0173 can close. No Phase B work required.

### 7.2 FIXME 0172 — short-name fallback chains

`fqtn_for_bare_type_name` cleanup is Part 2 of this plan. `defining_module_for` was already cleaned at S67 (per FIXME 0172 update note); `trait_home_for` is the post-cleanup precedent.

**Disposition**: **closeable upon Wave 3b landing Part 2**. The FIXME's "deferred-with-named-residue" note tied closure to FIXME 0187; that's still the gate for the `defining_module_for` consumer-side narrowing, but the **typecheck-internal** Principle 17 violation (the hardcoded fallback) closes with Part 2.

Recommend: after Wave 3b lands Part 2, **leave FIXME 0172 open** but update its status note to "narrowed to FIXME 0187 dependency only — internal fallback removed Sprint 72 Wave 3b". The `/sprint` skill closes the FIXME when 0187 lands.

### 7.3 FIXME 0098 — ResolutionGap/CheckError/ExpansionError migration

Phase 3 (typecheck): "Migrate `check_form` from `TypeCheckEnv` method form to free-function form" + "Return type changes from `Result<FormCheckResult, CranelispError>` to `Result<CheckResult, CheckError>`".

Verified: `check_forms` is the free function returning `Result<(), CheckError>` per `public-api.txt:152`. Phase 3's typecheck items are landed.

**Disposition**: **typecheck-side closeable** — no typecheck-side work implied by Phase B. Remaining open phases are frontend + int. Recommend: amend FIXME 0098 with a typecheck-side checkmark or defer to host-wiring sprint per original triage.

---

## Part 8 — Wave 3b execution order

Recommended order:

1. **Part 3 Step A** (MonoDefn population stop) — smallest, independent. Validates Wave 3b gate (existing tests stay green).
2. **Part 1.2 + 1.3 + 1.5 + 1.4** (IntrinsicType activation) — the core defect fix; flips the 26 failing tests green.
3. **Parts 2 + 2b + 5 as a single coherent change-set** — execute per the 6-step sub-order in "Cross-cutting: Parts 2 + 2b + 5 compose" above. Combines: `fqtn_for_bare_type_name` cleanup (Part 2), Tier 2 universe-walk delete (Part 2b), and the `ResolveError` + `resolve_*` family rename (Part 5). Pairs naturally with Part 1.4's impl-machinery dispatch.
4. **Part 4 A1 + A4 + A7** (module_aliases threading + env accessors) — single coherent source-moves change-set.
5. **Part 4 A2 partial** (`register_imports`/`register_exports` narrowing) — bundles with #4.
6. **Audit closure on FIXMEs 0172, 0173, 0098** — verification + status updates; no source change.
7. **File FIXME `target: /arch`** after #3 lands — facade-side rename cascade for `resolve_trait` / `resolve_type` / `resolve_constructor` in `facades/typecheck.md` (Phase C concern; `/dev` does not edit the facade per boundary).

Wave 3b acceptance:
- 26 failing tests flip green.
- `cargo nextest run -p cranelisp-typecheck` clean.
- `public-api.txt` regenerates per baseline-diff discipline; diff shows:
  - `+ module_aliases` parameters on check_forms / register_imports / register_exports
  - `+ TypeCheckEnv::current_symbol_table[_mut]`
  - `+ KnownTypeKind` (if elevated to public, else `pub(crate)`)
  - `+ pub enum ResolveError`, `+ pub fn resolve_trait`, `+ pub fn resolve_type`, `+ pub fn resolve_constructor` on `TypeChecker`
  - `- pub fn trait_home_for`, `- pub fn fqtn_for_bare_type_name`, `- pub fn lookup_constructor_type[_in_module/_with_state]` (those that were `pub`)
- Facade compliance test continues green; **facade-side rename cascade (`facades/typecheck.md`) is Phase C work, filed as FIXME `target: /arch`**.

## Next skills

- `/dev typecheck` — Wave 3b implementation following this plan.
- `/qa` — confirm test suite post-Wave-3b; no new tests mandated.
- `/review` typecheck — Wave 3b /review gate.
- `/arch` — FIXME 0239 architectural disposition (out of Phase B; informs longer-term Option A migration of intrinsic seeding to `cranelisp-primitives`).
