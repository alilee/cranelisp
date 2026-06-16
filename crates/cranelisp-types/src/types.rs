use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::{FQTraitName, FQTypeName, ModuleFullPath, TypeName};

/// Type variable identifier. Narrow to u32 -- 4 billion type vars sufficient.
pub type TypeId = u32;

/// Concrete type.
///
/// All variants exist from Ring 0. Ring 0 exercises Int, Bool, Float, simple Fn, Var,
/// and ADT (enum-only). Ring 1 adds String, ADT with fields, Fn-with-closures.
/// Ring 2 adds constrained Var usage and TyConApp.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Type {
    Int,
    Bool,
    String,
    Float,
    /// Function type: param types -> return type
    Fn(Vec<Type>, Box<Type>),
    /// Algebraic data type: fully-qualified type name + type arguments.
    /// Module context embedded at construction time — eliminates `build_type_modules()`.
    ADT(FQTypeName, Vec<Type>),
    /// Unification variable (inference internal; resolved before codegen)
    Var(TypeId),
    /// Type constructor application (higher-kinded types, Ring 2+)
    TyConApp(TypeId, Vec<Type>),
}

impl Type {
    /// Check whether this type is `IO _`.
    pub fn is_io(&self) -> bool {
        matches!(self, Type::ADT(fqtn, _) if fqtn.module == "primitives" && fqtn.name == "IO")
    }

    /// Extract the inner type from `IO T`.
    ///
    /// Returns a borrow of the inner type (e.g., `&Int` from `IO Int`).
    /// If the type is not IO or has no type arguments, returns `self` unchanged.
    pub fn unwrap_io(&self) -> &Type {
        match self {
            Type::ADT(_, args) if !args.is_empty() => &args[0],
            _ => self,
        }
    }

    /// Create a named ADT type with module qualification.
    pub fn adt(module: ModuleFullPath, name: TypeName, args: Vec<Type>) -> Type {
        Type::ADT(FQTypeName::new(module, name), args)
    }

    /// Returns true if this type contains any unresolved type variable (`Type::Var`).
    /// Used in `debug_assert!` to verify all types are fully resolved before codegen.
    pub fn contains_var(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Fn(params, ret) => {
                params.iter().any(|p| p.contains_var()) || ret.contains_var()
            }
            Type::ADT(_, args) | Type::TyConApp(_, args) => {
                args.iter().any(|a| a.contains_var())
            }
            Type::Int | Type::Bool | Type::String | Type::Float => false,
        }
    }

    /// Returns true if this type is **fully concrete** — no `Type::Var` (and no
    /// `Type::TyConApp`, whose head is itself a type variable) anywhere in its
    /// structure.
    ///
    /// **This is the GOT-slot eligibility predicate** (Principle 20, BC §7
    /// "Callability is structural"). The architectural invariant is: a def has a
    /// GOT slot **iff** its type is fully concrete. "Concrete" is *strictly
    /// stronger* than "unconstrained" (no trait bounds): a generic-but-
    /// unconstrained def (`id : ∀a. a→a`, or a HOF whose result is `(Box a)`)
    /// carries **zero** trait constraints yet is **not** concrete. Gating GOT-slot
    /// allocation on constraint-emptiness instead of concreteness was the leak that
    /// let a non-concrete def reach codegen as a value (S84 — the `(Box a)`-through-
    /// HOF SIGSEGV). The slot-allocation gate MUST test `is_concrete()`, not
    /// `constraints.is_empty()`.
    ///
    /// `TyConApp` is treated as non-concrete because its `TypeId` head is an
    /// unresolved higher-kinded type variable; a `TyConApp` reaching the slot gate
    /// is by construction not a monomorphised concrete callable.
    ///
    /// Equivalent today to `!self.contains_var()` for the first-order fragment;
    /// named separately because it expresses the *eligibility* intent at the gate
    /// (the inverse `contains_var` expresses the *debug-tripwire* intent at
    /// codegen), and because the `TyConApp`-head case is part of "concrete" but is
    /// not a bare `Var`.
    pub fn is_concrete(&self) -> bool {
        match self {
            Type::Var(_) => false,
            // A type-constructor application's head is an unresolved HKT variable;
            // a concrete callable never carries one at the slot gate.
            Type::TyConApp(_, _) => false,
            Type::Fn(params, ret) => {
                params.iter().all(|p| p.is_concrete()) && ret.is_concrete()
            }
            Type::ADT(_, args) => args.iter().all(|a| a.is_concrete()),
            Type::Int | Type::Bool | Type::String | Type::Float => true,
        }
    }

    /// Whether this type, at a codegen/RC site, carries a **representation-
    /// undetermined free `Type::Var`** — a value whose machine shape (heap
    /// pointer vs bare scalar/tag) cannot be decided because an unpinned type
    /// variable rides in a position where the representation depends on it.
    ///
    /// **THE single source of truth** for the §3.11.1 codegen-reaching ambiguity
    /// question, shared by two consumers so that typecheck and backend agree **by
    /// construction** (Principle 7, Principle 18; FIXME 0379, belt-and-braces
    /// ruling 2026-06-16):
    ///
    /// - **Typecheck (position-complete §3.11.1 check, FIXME 0379).** Calls this
    ///   on the resolved type at **every** codegen-reaching value position (match
    ///   scrutinees, fn-call args, vec elements, ctor fields, if-branches, ParBind
    ///   bindings, returns, nested lets — not just `let` bindings) and raises an
    ///   "ambiguous type" error when it is `true`. The predicate is **directly**
    ///   the ambiguity verdict here: under full monomorphisation-from-roots a
    ///   *genuinely free* var in a codegen-reaching position means **no root pins
    ///   it** — the program is ambiguous (0373(ii)) regardless of the value's heap
    ///   category, so the conservative `true` is a *correct* rejection, never a
    ///   false positive.
    /// - **Backend (`HeapCategory::classify`/`emit_rc_*` backstop, FIXME 0375).**
    ///   Gates this **behind its own `classify == Mixed` verdict**: panics at an RC
    ///   site iff `classify(ty, tables) == Mixed && ty.is_representation_undetermined()`.
    ///   The `Mixed` gate is what excludes a table-determined `NeverHeap`
    ///   (all-nullary `(Phantom a)`) or `AlwaysHeap` (all-data) ADT that this
    ///   table-free predicate cannot itself rule out — so the backend never panics
    ///   on a representation-*determined* ADT even when it carries a free var, while
    ///   the typecheck side legitimately rejects it as ambiguous.
    ///
    /// **Matches the backend `classify` ground truth** (`crates/cranelisp-backend/
    /// src/heap.rs`): the two `classify` arms that return `Mixed`-with-an-unpinned-
    /// representation are `Type::Var`/`Type::TyConApp` (no static knowledge) and a
    /// `Type::ADT` whose ctor shape is `Mixed` (`(has_nullary, has_data) ==
    /// (true, true)`) — and the dangerous ADT case is *exactly* a `Mixed`-shaped ADT
    /// carrying a free var (the `<1024` RC-guard use-after-free, FIXME 0374/0375).
    /// The structural predicate captures the "carries a free var in a
    /// representation-bearing position" half table-free; the backend supplies the
    /// "is `Mixed`-shaped" half from the symbol tables. They agree on the dangerous
    /// core by construction.
    ///
    /// **TRUE** for: a bare `Type::Var`; a `Type::TyConApp` (its `TypeId` head is
    /// an unpinned HKT var); a non-`Vec` `Type::ADT` carrying a free `Type::Var`
    /// anywhere in its args (`(Option a)`, `(Box a)` — the case the bare-`Var`
    /// panic misses, the FIXME-0379 hole).
    ///
    /// **FALSE** for: `Type::Fn` (always a heap closure — word-represented, RC
    /// uniform, sound regardless of any free var); `(Vec a)` (the `Vec` builtin is
    /// uniformly heap-allocated — RC is element-type-independent); any fully
    /// concrete type; and a `Type::ADT` with **no** free var (the legitimate
    /// type-known nullary-tag `Mixed`-discrimination case the `<1024` guard is
    /// *kept* for).
    ///
    /// Note the `Vec`/`Fn` exclusions are the *structurally uniformly-heap* set —
    /// the same set `classify` routes to `AlwaysHeap` independent of the free var.
    /// The `Vec` exclusion is keyed on the bare type name (`fqtn.name == "Vec"`),
    /// mirroring `classify_adt`'s short-circuit; if a second uniformly-heap builtin
    /// is ever added, both sites update in lockstep (the stringly-typed coupling
    /// /review flagged under FIXME 0379 — minor, noted, not part of the hole).
    pub fn is_representation_undetermined(&self) -> bool {
        match self {
            // No static representation knowledge — the dangerous bare-var shape.
            Type::Var(_) => true,
            // The HKT head is itself an unpinned type variable.
            Type::TyConApp(_, _) => true,
            // Always a heap closure — word-represented, RC-uniform: representation
            // is determined despite any free var in the signature.
            Type::Fn(_, _) => false,
            Type::ADT(fqtn, args) => {
                // `Vec` is uniformly heap-allocated — RC is independent of the
                // element type, so a polymorphic `(Vec a)` is representation-
                // DETERMINED (matches `classify_adt`'s `AlwaysHeap` short-circuit).
                if fqtn.name.as_ref() == "Vec" {
                    return false;
                }
                // A non-`Vec` ADT carrying a free var anywhere in its args is the
                // representation-undetermined shape (the `(Option a)`/`(Box a)`
                // family). With NO free var it is representation-determined (the
                // legitimate type-known nullary-tag `Mixed` case → FALSE).
                args.iter().any(|a| !free_vars(a).is_empty())
            }
            Type::Int | Type::Bool | Type::String | Type::Float => false,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Float => write!(f, "Float"),
            Type::Fn(params, ret) => {
                write!(f, "(Fn [")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, "] {ret})")
            }
            Type::ADT(fqtn, args) => {
                if args.is_empty() {
                    write!(f, "{fqtn}")
                } else {
                    write!(f, "({fqtn}")?;
                    for a in args {
                        write!(f, " {a}")?;
                    }
                    write!(f, ")")
                }
            }
            Type::Var(id) => write!(f, "t{id}"),
            Type::TyConApp(id, args) => {
                write!(f, "(TyCon t{id}")?;
                for a in args {
                    write!(f, " {a}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Polymorphic type scheme: universally quantified type with optional trait constraints.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scheme {
    /// Quantified type variables
    pub type_vars: Vec<TypeId>,
    /// Trait constraints on type variables: TypeId -> list of required fully-qualified trait names
    pub constraints: HashMap<TypeId, Vec<FQTraitName>>,
    /// The underlying type
    pub ty: Type,
}

/// Map from internal TypeId to user-friendly type variable name (a, b, c, ...).
///
/// Collects all Var ids in order of first occurrence, then assigns sequential
/// names. Used by REPL display and Scheme formatting.
pub fn type_var_names(ty: &Type) -> HashMap<TypeId, String> {
    let mut ids = Vec::new();
    collect_var_ids_ordered(ty, &mut ids);
    ids.into_iter()
        .enumerate()
        .map(|(i, id)| {
            let name = if i < 26 {
                String::from((b'a' + i as u8) as char)
            } else {
                format!("t{id}")
            };
            (id, name)
        })
        .collect()
}

/// Format a type with user-friendly variable names (a, b, c, ...).
///
/// Replaces internal TypeId numbers with sequential letters.
pub fn format_type_display(ty: &Type) -> String {
    let names = type_var_names(ty);
    format_type_with_vars(ty, &names)
}

/// Format a type using the given variable name mapping.
pub fn format_type_with_vars(ty: &Type, var_names: &HashMap<TypeId, String>) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Float => "Float".to_string(),
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_type_with_vars(p, var_names))
                .collect();
            let ret_s = format_type_with_vars(ret, var_names);
            format!("(Fn [{}] {ret_s})", parts.join(" "))
        }
        Type::ADT(fqtn, args) => {
            if args.is_empty() {
                format!("{fqtn}")
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_with_vars(a, var_names))
                    .collect();
                format!("({fqtn} {})", arg_strs.join(" "))
            }
        }
        Type::Var(id) => {
            var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"))
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if args.is_empty() {
                name
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_with_vars(a, var_names))
                    .collect();
                format!("({name} {})", arg_strs.join(" "))
            }
        }
    }
}

/// Collect Var ids in order of first occurrence (left-to-right, depth-first).
fn collect_var_ids_ordered(ty: &Type, ids: &mut Vec<TypeId>) {
    match ty {
        Type::Var(id) => {
            if !ids.contains(id) {
                ids.push(*id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids_ordered(p, ids);
            }
            collect_var_ids_ordered(ret, ids);
        }
        Type::ADT(_, args) | Type::TyConApp(_, args) => {
            for a in args {
                collect_var_ids_ordered(a, ids);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

/// Type substitution: mapping from type variables to concrete types.
pub type Subst = HashMap<TypeId, Type>;

/// Apply a substitution to a type, replacing Var(id) with the mapped type.
/// Recursively applies until no more substitutions can be made.
pub fn apply(subst: &Subst, ty: &Type) -> Type {
    match ty {
        Type::Var(id) => {
            if let Some(mapped) = subst.get(id) {
                // Defensive cycle guard: a well-formed substitution never maps
                // a variable (transitively) to a type containing itself — that
                // is an occurs-check violation. If one is ever constructed
                // (see FIXME 0279/0295: a cross-module instantiation building
                // an identity self-map `{id -> Var(id)}` when the fresh-var
                // counter collides with an imported scheme's bound vars), the
                // naive chase `apply(subst, mapped)` recurses forever and
                // overflows the stack. Detect a direct self-map and treat the
                // variable as unbound rather than diverging. Instantiation is
                // fixed at construction (typecheck `fresh_instantiation_subst`)
                // so this guard should never fire in practice; the
                // `debug_assert!` surfaces it as a clear failure in debug
                // builds, and the fallthrough keeps release builds bounded.
                if let Type::Var(mapped_id) = mapped
                    && mapped_id == id
                {
                    debug_assert!(
                        false,
                        "apply: cyclic substitution — Var({id}) maps to itself (occurs-check violation)"
                    );
                    return ty.clone();
                }
                apply(subst, mapped)
            } else {
                ty.clone()
            }
        }
        Type::Fn(params, ret) => {
            let params = params.iter().map(|p| apply(subst, p)).collect();
            let ret = Box::new(apply(subst, ret));
            Type::Fn(params, ret)
        }
        Type::ADT(name, args) => {
            let args = args.iter().map(|a| apply(subst, a)).collect();
            Type::ADT(name.clone(), args)
        }
        Type::TyConApp(id, args) => {
            let applied_args: Vec<Type> = args.iter().map(|a| apply(subst, a)).collect();
            // If the constructor variable is in the substitution, remap:
            // - subst[id] = ADT(name, []) → ADT(name, applied_args)
            // - subst[id] = Var(other_id) → TyConApp(other_id, applied_args)
            if let Some(mapped) = subst.get(id) {
                let resolved = apply(subst, mapped);
                match resolved {
                    Type::ADT(name, _) => Type::ADT(name, applied_args),
                    Type::Var(other_id) => Type::TyConApp(other_id, applied_args),
                    _ => Type::TyConApp(*id, applied_args),
                }
            } else {
                Type::TyConApp(*id, applied_args)
            }
        }
        // Primitive types are not affected by substitution.
        Type::Int | Type::Bool | Type::String | Type::Float => ty.clone(),
    }
}

/// Find the maximum TypeId used in a type (including in Var and TyConApp).
///
/// Returns `None` if the type contains no type variables or type constructors.
/// Used to advance the typechecker's `next_id` past type vars from cached modules
/// to prevent ID collisions during instantiation.
pub fn max_type_var_id(ty: &Type) -> Option<TypeId> {
    let mut max_id: Option<TypeId> = None;
    collect_max_type_var_id(ty, &mut max_id);
    max_id
}

fn collect_max_type_var_id(ty: &Type, max_id: &mut Option<TypeId>) {
    match ty {
        Type::Var(id) => {
            *max_id = Some(max_id.map_or(*id, |m| m.max(*id)));
        }
        Type::TyConApp(id, args) => {
            *max_id = Some(max_id.map_or(*id, |m| m.max(*id)));
            for a in args {
                collect_max_type_var_id(a, max_id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_max_type_var_id(p, max_id);
            }
            collect_max_type_var_id(ret, max_id);
        }
        Type::ADT(_, args) => {
            for a in args {
                collect_max_type_var_id(a, max_id);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

/// Collect free (unbound) type variables in a type.
pub fn free_vars(ty: &Type) -> HashSet<TypeId> {
    let mut result = HashSet::new();
    collect_free_vars(ty, &mut result);
    result
}

fn collect_free_vars(ty: &Type, result: &mut HashSet<TypeId>) {
    match ty {
        Type::Var(id) => {
            result.insert(*id);
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_free_vars(p, result);
            }
            collect_free_vars(ret, result);
        }
        Type::ADT(_, args) => {
            for a in args {
                collect_free_vars(a, result);
            }
        }
        Type::TyConApp(con_id, args) => {
            // The constructor ID itself is a type variable for occurs-check purposes
            result.insert(*con_id);
            for a in args {
                collect_free_vars(a, result);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test helper: create an FQTypeName in a "test" module.
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    /// Test helper: create an FQTypeName in the "primitives" module.
    fn primitives_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
    }

    // Decision 0047 (FQTypeName binding) cement. `Type::adt` is the one
    // constructor inside cranelisp-types that takes a bare `TypeName` and lifts
    // it to the fully-qualified `Type::ADT(FQTypeName, _)` form — the single
    // place a bare-name leak could originate from within the crate. This test
    // pins (a) the module context is preserved (non-empty, == the supplied
    // module), and (b) module is load-bearing for identity — same local name in
    // different modules produces distinct, unequal ADT types. A regression that
    // dropped the module qualification (the FQTypeName leak Decision 0047
    // forbids) is caught here. See design/arch/bounded-contexts.md §7.
    #[test]
    fn test_adt_construction_is_fully_qualified() {
        let ty = Type::adt(
            ModuleFullPath::from("option"),
            TypeName::from("Option"),
            vec![Type::Int],
        );
        match &ty {
            Type::ADT(fq, args) => {
                assert!(!fq.module.is_empty(), "FQTypeName module must be populated");
                assert_eq!(fq.module, "option", "module context must be preserved");
                assert_eq!(fq.name, "Option");
                assert_eq!(args, &vec![Type::Int]);
            }
            other => panic!("Type::adt must produce Type::ADT, got {other:?}"),
        }
    }

    #[test]
    fn test_adt_same_name_different_module_are_distinct() {
        let a = Type::adt(ModuleFullPath::from("foo"), TypeName::from("T"), vec![]);
        let b = Type::adt(ModuleFullPath::from("bar"), TypeName::from("T"), vec![]);
        // Module is load-bearing for identity — a bare-name-only ADT would
        // collapse these to equal, which Decision 0047 forbids.
        assert_ne!(a, b, "same local name in different modules must not be equal");
    }

    #[test]
    fn test_apply_identity() {
        let subst = Subst::new();
        assert_eq!(apply(&subst, &Type::Int), Type::Int);
    }

    #[test]
    fn test_apply_var_substitution() {
        let mut subst = Subst::new();
        subst.insert(0, Type::Int);
        assert_eq!(apply(&subst, &Type::Var(0)), Type::Int);
    }

    // FIXME 0279/0295 — defensive cycle guard. A well-formed substitution
    // never maps a var to itself; if a pathological self-map `{0 -> Var(0)}`
    // is ever constructed, `apply` must NOT recurse forever. In debug builds
    // the `debug_assert!` surfaces the occurs-check violation as a panic; in
    // release builds the fallthrough keeps it bounded (returns the var).
    #[test]
    #[cfg_attr(debug_assertions, should_panic(expected = "cyclic substitution"))]
    fn test_apply_self_map_does_not_overflow() {
        let mut subst = Subst::new();
        subst.insert(0, Type::Var(0)); // identity self-map
        // Must terminate (panic in debug via the guard; bounded in release).
        let result = apply(&subst, &Type::Var(0));
        // Reached only in release builds — the guard returns the var unchanged.
        assert_eq!(result, Type::Var(0));
    }

    #[test]
    fn test_apply_fn_substitution() {
        let mut subst = Subst::new();
        subst.insert(0, Type::Int);
        let fn_type = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
        let expected = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        assert_eq!(apply(&subst, &fn_type), expected);
    }

    #[test]
    fn test_free_vars() {
        let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
        let fv = free_vars(&ty);
        assert!(fv.contains(&0));
        assert!(fv.contains(&1));
        assert_eq!(fv.len(), 2);
    }

    #[test]
    fn test_free_vars_no_vars() {
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        let fv = free_vars(&ty);
        assert!(fv.is_empty());
    }

    #[test]
    fn test_contains_var_primitive() {
        assert!(!Type::Int.contains_var());
        assert!(!Type::Bool.contains_var());
        assert!(!Type::String.contains_var());
        assert!(!Type::Float.contains_var());
    }

    #[test]
    fn test_contains_var_direct() {
        assert!(Type::Var(0).contains_var());
    }

    #[test]
    fn test_contains_var_nested_fn() {
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Var(0)));
        assert!(ty.contains_var());

        let ty2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        assert!(!ty2.contains_var());
    }

    #[test]
    fn test_contains_var_nested_adt() {
        let ty = Type::ADT(test_fqtn("Option"), vec![Type::Var(0)]);
        assert!(ty.contains_var());

        let ty2 = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
        assert!(!ty2.contains_var());
    }

    // Principle 20 / BC §7 "Callability is structural": `is_concrete` is the
    // GOT-slot-eligibility predicate. "Concrete" is strictly stronger than
    // "unconstrained" — a generic-but-unconstrained type is NOT concrete.
    #[test]
    fn test_is_concrete_primitive() {
        assert!(Type::Int.is_concrete());
        assert!(Type::Bool.is_concrete());
        assert!(Type::String.is_concrete());
        assert!(Type::Float.is_concrete());
    }

    #[test]
    fn test_is_concrete_var_is_not() {
        // The leak case: a bare type var is not concrete (no slot).
        assert!(!Type::Var(0).is_concrete());
        // ∀a. a→a (the `id` shape): unconstrained, but NOT concrete.
        let id = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
        assert!(!id.is_concrete());
    }

    #[test]
    fn test_is_concrete_adt_field_var_is_not() {
        // The S84 SIGSEGV shape: a HOF result `(Box a)` carries a Type::Var
        // field — non-concrete, must NOT be slotted.
        let box_a = Type::ADT(test_fqtn("Box"), vec![Type::Var(0)]);
        assert!(!box_a.is_concrete());
        // Its monomorphised instance `(Box Int)` IS concrete (gets a slot).
        let box_int = Type::ADT(test_fqtn("Box"), vec![Type::Int]);
        assert!(box_int.is_concrete());
    }

    #[test]
    fn test_is_concrete_nested_fn() {
        let concrete = Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::String));
        assert!(concrete.is_concrete());
        let leaky = Type::Fn(vec![Type::Int], Box::new(Type::Var(7)));
        assert!(!leaky.is_concrete());
    }

    #[test]
    fn test_is_concrete_tyconapp_is_not() {
        // A type-constructor application's head is an unresolved HKT var.
        assert!(!Type::TyConApp(0, vec![Type::Int]).is_concrete());
    }

    #[test]
    fn test_is_concrete_is_inverse_of_contains_var_first_order() {
        // For the first-order fragment, is_concrete == !contains_var.
        for ty in [
            Type::Int,
            Type::Fn(vec![Type::Int], Box::new(Type::Bool)),
            Type::Fn(vec![Type::Var(0)], Box::new(Type::Bool)),
            Type::ADT(test_fqtn("Box"), vec![Type::Var(1)]),
        ] {
            assert_eq!(ty.is_concrete(), !ty.contains_var(), "{ty}");
        }
    }

    // FIXME 0379 (belt-and-braces, user-ruled 2026-06-16): the shared
    // `is_representation_undetermined` predicate is THE single source of truth
    // for "does this type carry a representation-undetermined free `Type::Var` at
    // a codegen/RC site." Typecheck uses it directly (position-complete §3.11.1
    // ambiguity check); backend gates it behind `classify == Mixed` (FIXME 0375
    // backstop). These tests pin the dangerous/safe split named in the ruling:
    // Option-a TRUE, Box-a TRUE, bare-Var TRUE, Vec-a FALSE, Fn-a FALSE,
    // Option-Int FALSE, Int FALSE. See design/arch/bounded-contexts.md §3 inv 9.
    #[test]
    fn test_repr_undetermined_bare_var_is_true() {
        // No static representation knowledge — the canonical dangerous shape.
        assert!(Type::Var(0).is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_tyconapp_is_true() {
        // HKT head is an unpinned type variable.
        assert!(Type::TyConApp(0, vec![Type::Int]).is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_option_a_is_true() {
        // (Option a) — the Mixed-ADT-with-free-var family the bare-Var panic
        // misses (the FIXME 0379 hole).
        let option_a = Type::ADT(test_fqtn("Option"), vec![Type::Var(0)]);
        assert!(option_a.is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_box_a_is_true() {
        // (Box a) — the HOF-result shape that SIGSEGV'd through the slot gate.
        let box_a = Type::ADT(test_fqtn("Box"), vec![Type::Var(0)]);
        assert!(box_a.is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_option_int_is_false() {
        // Fully concrete ADT — representation determined, NOT ambiguous.
        let option_int = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
        assert!(!option_int.is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_vec_a_is_false() {
        // (Vec a) — uniformly heap-allocated; RC is element-type-independent,
        // so a polymorphic Vec is representation-DETERMINED (matches
        // classify_adt's AlwaysHeap short-circuit).
        let vec_a = Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![Type::Var(0)],
        );
        assert!(!vec_a.is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_fn_a_is_false() {
        // (Fn [a] a) — always a heap closure, word-represented, RC-uniform:
        // representation is determined despite the free var.
        let fn_a = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
        assert!(!fn_a.is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_int_is_false() {
        // Primitives are fully concrete — never undetermined.
        assert!(!Type::Int.is_representation_undetermined());
        assert!(!Type::Bool.is_representation_undetermined());
        assert!(!Type::String.is_representation_undetermined());
        assert!(!Type::Float.is_representation_undetermined());
    }

    #[test]
    fn test_repr_undetermined_nested_adt_free_var_is_true() {
        // (Option (Box a)) — the free var rides nested; still undetermined.
        let inner = Type::ADT(test_fqtn("Box"), vec![Type::Var(0)]);
        let nested = Type::ADT(test_fqtn("Option"), vec![inner]);
        assert!(nested.is_representation_undetermined());
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Type::Int), "Int");
        let fn_ty = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        assert_eq!(format!("{fn_ty}"), "(Fn [Int Int] Int)");
        let adt = Type::ADT(test_fqtn("Color"), vec![]);
        assert_eq!(format!("{adt}"), "test/Color");
    }

    // --- IO type detection ---

    // spec: 10-io §10.6.1 — Type::is_io detects IO ADT
    #[test]
    fn test_is_io_positive() {
        let io_int = Type::ADT(primitives_fqtn("IO"), vec![Type::Int]);
        assert!(io_int.is_io());
    }

    // spec: 10-io §10.6.1 — Type::is_io rejects non-IO types
    #[test]
    fn test_is_io_negative() {
        assert!(!Type::Int.is_io());
        assert!(!Type::Bool.is_io());
        let option_int = Type::ADT(test_fqtn("Option"), vec![Type::Int]);
        assert!(!option_int.is_io());
    }

    // spec: 10-io §10.6.1 — Type::is_io rejects user-defined IO type in wrong module
    #[test]
    fn test_is_io_wrong_module() {
        let user_io = Type::ADT(test_fqtn("IO"), vec![Type::Int]);
        assert!(!user_io.is_io());
    }

    // spec: 10-io §10.6.1 — Type::unwrap_io unwraps IO
    #[test]
    fn test_unwrap_io() {
        let io_int = Type::ADT(primitives_fqtn("IO"), vec![Type::Int]);
        assert_eq!(io_int.unwrap_io(), &Type::Int);

        let io_string = Type::ADT(primitives_fqtn("IO"), vec![Type::String]);
        assert_eq!(io_string.unwrap_io(), &Type::String);
    }

    // spec: 10-io §10.8 — Type::unwrap_io fallback for non-IO
    #[test]
    fn test_unwrap_io_no_args() {
        let io_bare = Type::ADT(primitives_fqtn("IO"), vec![]);
        assert_eq!(io_bare.unwrap_io(), &io_bare);
    }

    // --- U1.6: type variable display name tests ---

    #[test]
    fn test_format_type_display_single_var() {
        // A single type variable should display as "a", not "t42".
        let ty = Type::Var(42);
        assert_eq!(format_type_display(&ty), "a");
    }

    #[test]
    fn test_format_type_display_identity_fn() {
        // (Fn [Var(5)] Var(5)) should display as "(Fn [a] a)".
        let ty = Type::Fn(vec![Type::Var(5)], Box::new(Type::Var(5)));
        assert_eq!(format_type_display(&ty), "(Fn [a] a)");
    }

    #[test]
    fn test_format_type_display_two_vars() {
        // Two distinct vars should be "a" and "b".
        let ty = Type::Fn(vec![Type::Var(10), Type::Var(20)], Box::new(Type::Var(10)));
        assert_eq!(format_type_display(&ty), "(Fn [a b] a)");
    }

    #[test]
    fn test_format_type_display_concrete_type() {
        // Concrete types should display normally.
        assert_eq!(format_type_display(&Type::Int), "Int");
        assert_eq!(format_type_display(&Type::Bool), "Bool");
    }

    #[test]
    fn test_format_type_display_polymorphic_adt() {
        // (test/Option Var(3)) should display as "(test/Option a)".
        let ty = Type::ADT(test_fqtn("Option"), vec![Type::Var(3)]);
        assert_eq!(format_type_display(&ty), "(test/Option a)");
    }

    #[test]
    fn test_type_var_names_ordering() {
        // Variable names assigned in order of first occurrence.
        let ty = Type::Fn(
            vec![Type::Var(99), Type::Var(50)],
            Box::new(Type::Var(99)),
        );
        let names = type_var_names(&ty);
        assert_eq!(names.get(&99), Some(&"a".to_string()));
        assert_eq!(names.get(&50), Some(&"b".to_string()));
    }
}
