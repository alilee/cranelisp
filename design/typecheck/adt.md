# ADT Type Checking

Solution design for algebraic data type (ADT) type checking in Cranelisp. Covers type definition registration, constructor scheme generation, pattern matching inference, and exhaustiveness checking.

## Type Definition Registration

Registration happens in `adt.rs` via `TypeChecker::register_type_def`. The process handles both nullary enums (Ring 0) and parameterized ADTs with data constructor fields (Ring 1).

### Registration Pipeline

```
register_type_def(name, type_params, constructors, ...)
  1. allocate_type_params     → (var_map, type_var_ids)
  2. build ADT result type   → Type::ADT(name, [Var(id) for id in type_var_ids])
  3. build_constructor_infos  → Vec<ConstructorInfo> with resolved field types
  4. register_constructors    → symbol table + constructor_to_type map
  5. find_same_name_ctor      → handle product type case
  6. register TypeDef entry   → symbol table
```

> **Dotted `Type.Ctor` canonical keys (S109 bucket 2).** As of the dotted-ctor
> capability, `register_constructors` stores a **sum** ctor's real got-slotted
> `Def` under the canonical key `member_key(Type, Ctor)` (`Maybe.Some`) with the
> bare ctor name as a poisoning `Import` alias — the exact mirror of the field
> accessor's `Type.field` canonical/bare-alias storage. Same-named ctors across
> in-scope types coexist; the dotted form disambiguates in value AND pattern
> position. A **product** ctor keeps its single type-name key (the dual facet
> below); its dotted form is degenerate. Full design:
> **`design/typecheck/dotted-ctor-registration.md`**.

> **Field-accessor synthesis is slot-gated (S119, FIXME 0924).**
> `synthesise_one_accessor` (`adt.rs:618-637`) mints the canonical `Type.field`
> `Def` as `UserFnState::Concrete { got_slot }` **unconditionally** — including for
> a polymorphic product, whose scheme `∀a. (Fn [(Bx a)] a)` is not
> `Type::is_concrete()`. That is the pairing `monomorphisation.md` §2.1 declares
> unconstructable, and the compiled frame is memory-unsafe at the
> `NULLARY_TAG_THRESHOLD` boundary (`design/backend/non-concrete-release-contract.md`
> §2.4). Ruled: the mint takes the universal gate (**P-1**), a non-concrete accessor
> becomes slot-less `Polymorphic`, and its instances are produced by **re-running
> this synthesiser at concrete type arguments** (**A-MINT**) rather than by a body
> re-check — the body is `Span::SYNTHETIC` and outside span-keyed carrier transport.
> The bare-alias `Import` edge, the §8.6.5 `Ambiguous` contest and the impl-time
> collision pre-flight are **untouched**: they key on the canonical entry, not its
> `fn_state`. **Rider 0867** (accessor synthesis over every constructor arm)
> unblocks on P-1 alone. Full statement:
> **`non-concrete-producer-obligations.md`**.

### Type Parameter Allocation

Each type parameter (e.g., `a` in `(deftype (Option a) ...)`) gets a fresh type variable via `fresh_var_id`. The `var_map` (HashMap<Symbol, TypeId>) maps parameter names to their allocated IDs, used by `resolve_type_expr` when processing field type annotations.

### Field Type Resolution

Field types are `TypeExpr` values from the frontend. Resolution via `resolve_type_expr`:

| TypeExpr | Resolution |
|----------|-----------|
| `Named("Int")` | `Type::Int` (primitive lookup) |
| `Named("Color")` | `Type::ADT("Color", [])` (known types lookup) |
| `TypeVar("a")` | `Type::Var(id)` (var_map lookup) |
| `Applied("Option", [Named("Int")])` | `Type::ADT("Option", [Type::Int])` (recursive + arity check) |
| `FnType(params, ret)` | `Type::Fn(resolved_params, resolved_ret)` |

### Arity Validation

`KnownTypes` is `HashMap<TypeName, usize>` — maps type names to their expected type parameter count. When resolving `TypeExpr::Applied(name, args)`:

- Look up expected arity in `KnownTypes`
- Compare `args.len()` against expected arity
- Return `TypeError` on mismatch: "type Option expects 1 type argument(s), got 2"

**Rejected alternative**: Using `HashMap<TypeName, ()>` (Ring 0 design) and looking up `TypeDefInfo` for arity. Changed to `HashMap<TypeName, usize>` because the arity is the only information needed, and this avoids a dependency on `TypeDefInfo` in the resolution path.

## Constructor Scheme Generation

`build_constructor_scheme` produces a polymorphic type scheme for each constructor:

### Nullary Constructors

```
(deftype (Option a) None ...)

None :: forall [a]. (Option a)
```

Scheme: `{ vars: [a_id], ty: ADT("Option", [Var(a_id)]) }`

### Data Constructors

```
(deftype (Option a) ... (Some [:a val]))

Some :: forall [a]. (Fn [a] (Option a))
```

Scheme: `{ vars: [a_id], ty: Fn([Var(a_id)], ADT("Option", [Var(a_id)])) }`

### Monomorphic Constructors

```
(deftype Point (Point [:Int x :Int y]))

Point :: (Fn [Int Int] Point)
```

Scheme: `{ vars: [], ty: Fn([Int, Int], ADT("Point", [])) }`

## Product Type Handling — the dual-facet constructor (S79 Option 3a, FIXME 0319)

When a single constructor has the same name as the type (e.g., `(deftype Rectangle [:Int w :Int h])`), a name collision occurs in the symbol table: the type name and the constructor name are one key.

**Design**: The surviving `"Rectangle"` entry is the **got-slotted constructor
`Def`** (exactly like a sum ctor) carrying a **type facet** —
`DefKind::Constructor { type_def: Some(Box<TypeDefInfo>), .. }`. A **sum/enum**
type instead registers a separate `ModuleEntry::TypeDef`, and its ctors carry
`type_def: None`. A product ctor's scheme lives canonically on its own
`Def.scheme` and its field names on `Def.param_names`. `is_product` is computed
in `adt.rs::register_type_def_with_ctor_infos` (`ctors.len()==1 &&
ctor-name==type-name`), which either registers a separate `TypeDef` (sum/enum)
OR attaches the facet to the lone ctor `Def` (product) — never both.

- **`checker::type_def_view_of(&ModuleEntry) -> Option<&TypeDefInfo>`** is the
  single "entry as a type" reader: `Some` for a `TypeDef`, OR for a product
  ctor's `type_def: Some(td)`. Every site needing an entry *as a type* routes
  through it (`ModuleReadView::lookup_type_def`, `resolve_type`,
  `concrete_type_for_impl_target`, and the `resolve.rs` source-annotation
  resolvers `resolve_named`/`resolve_applied` so a product type in TYPE position
  — `:Box`, `(Box Int)` — answers). Do NOT re-pattern `TypeDef` directly when a
  product type must also answer.
- **Product ctors do NOT auto-curry.** A product ctor's `Def.scheme` is
  curry-shaped (`Fn([Int,Int], Point)`), so an under-applied `(Point 1)` would
  otherwise fall into `infer.rs::try_auto_curry` and silently return a closure
  instead of an arity error. The guard at the top of `try_auto_curry` returns a
  `TypeError` ("constructor X expects N arguments but got M", spec §5.2.7) when
  the callee resolves to a `DefKind::Constructor` Def. Sum ctors hit the same
  guard.
- **Ctor → parent-type** lookups and **pattern-ctor resolution** read the `Def {
  kind: Constructor }.type_name` arm for products too — no product special-case.

**Retired smuggling**: the pre-S79 approach extracted the ctor scheme into a
`ModuleEntry::TypeDef.constructor_scheme` field, with `lookup_constructor_scheme`
and ~six bespoke fallback legs keyed on it. That field and its fallback legs are
**gone** — the scheme lives on the ctor's own `Def.scheme`, so type and ctor no
longer smuggle each other's data through a shared entry.

**Rejected alternative**: Renaming the constructor (e.g., `Mk` prefix). This would break the user-facing syntax where `(Point 1 2)` creates a `Point` value. The same-name convention is idiomatic for product types.

## Pattern Matching Inference

Constructor patterns in `match` expressions are checked by `check_constructor_pattern` in `infer.rs`.

### Algorithm

```
check_constructor_pattern(ctor_name, bindings, scrutinee_type, span)
  1. lookup_constructor_scheme(ctor_name)         → Scheme
  2. instantiate(scheme)                          → fresh instance
  3. Classify: nullary (Type::ADT) vs data (Type::Fn)
  4. For nullary: unify(ctor_type, scrutinee_type)
  5. For data (Fn [field_types...] result_type):
     a. Validate bindings.len() == field_types.len()
     b. unify(result_type, scrutinee_type)
     c. Bind each pattern var to apply_subst(field_type)
```

### Constructor Scheme Lookup

`lookup_constructor_scheme` searches these sources:

1. `type_defs.constructor_type(name)` → `type_defs.get(type_name)` → find constructor in `TypeDefInfo`
2. Symbol table: `ModuleEntry::Constructor { scheme, .. }` — this arm now serves **product ctors too**, since a product ctor is a got-slotted `Constructor` `Def` carrying its scheme on `Def.scheme` (see §"Product Type Handling"). The retired product-specific fallback leg keyed on `ModuleEntry::TypeDef.constructor_scheme` (S79, FIXME 0319) is deleted.

### Type Instantiation and Unification

Each match arm gets a fresh instantiation of the constructor's scheme. This ensures that pattern matching against a polymorphic constructor (like `Some`) correctly constrains the type variable for that arm.

Example:
```
(match opt
  [(Some x) x]       ;; instantiate Some: Fn [t42] (Option t42), unify (Option t42) with scrutinee
  [None default])     ;; instantiate None: (Option t43), unify with scrutinee
```

After unification, `x` has type `apply_subst(t42)` which resolves to the concrete element type.

## Exhaustiveness Checking

`check_exhaustiveness` verifies that a match covers all constructors of an ADT.

### Algorithm

```
check_exhaustiveness(type_name, covered_ctors, has_wildcard, span)
  if has_wildcard → ok (wildcard covers everything)
  all_ctors = type_def.constructors.map(name)
  missing = all_ctors - covered_ctors
  if missing.is_empty() → ok
  else → TypeError("non-exhaustive: missing X, Y")
```

### Properties

- Name-based: coverage is tracked by constructor name, not by pattern structure
- Works identically for nullary and data constructors (Ring 0 and Ring 1)
- Wildcard (`_`) or variable patterns bypass the constructor coverage check
- Missing constructors are sorted alphabetically in error messages for determinism

### Limitations (Ring 0-1)

- No nested pattern checking (e.g., `(Some (Some x))`)
- No literal pattern coverage (integers, strings)
- No guard analysis
- These are deferred to Ring 3+ or may not be needed depending on language evolution

## Per-Ring Evolution

### Ring 0

- Nullary enum constructors only (`(deftype Color Red Green Blue)`)
- Monomorphic constructor schemes
- Basic exhaustiveness checking
- Pattern matching on constructor name only (no bindings)

### Ring 1 — Current

- Polymorphic type parameters (`(deftype (Option a) ...)`)
- Data constructors with typed fields (`(Some [:a val])`)
- Constructor pattern bindings (`[(Some x) ...]`)
- `TypeExpr::Applied` resolution with arity validation
- Product type handling (same-name constructor/type)
- Shortcut syntax (`(deftype Pair [first second])`)

### Ring 2 — Planned

- Trait-constrained type parameters
- Polymorphic ADT trait implementations
- Monomorphisation of polymorphic ADT operations
- Field accessor functions
