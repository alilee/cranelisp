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

## Product Type Handling

When a single constructor has the same name as the type (e.g., `(deftype Point [:Int x :Int y])`), a name collision occurs in the symbol table: the `TypeDef` entry and `Constructor` entry compete for the same key.

**Solution**: The `Constructor` entry is registered first. When the `TypeDef` entry is registered (which overwrites the `Constructor`), the constructor's scheme is extracted and stored in `ModuleEntry::TypeDef { constructor_scheme: Some(scheme), ... }`. The `lookup_in_symbol_table` method checks for `TypeDef` entries with a `constructor_scheme` and returns the scheme when found.

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

`lookup_constructor_scheme` searches three sources:

1. `type_defs.constructor_type(name)` → `type_defs.get(type_name)` → find constructor in `TypeDefInfo`
2. Symbol table: `ModuleEntry::Constructor { scheme, .. }`
3. Symbol table: `ModuleEntry::TypeDef { constructor_scheme: Some(scheme), .. }` (product types)

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
