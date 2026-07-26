//! S118 W3 (FIXME 0892) — the registry's `GlueShape::Vec` arm is **RC-GATED**.
//!
//! `design/backend/transitive-drop-glue.md` §10 row 3's negative reads "no field
//! call on `old_rc > 1`". For every other shape that claim is emitted by
//! `emit_outer_drop`, which builds the gate itself; the `Vec` arm instead
//! delegates to `vec_codegen::emit_vec_rc_dec_with_drop`, because
//! `runtime/vec_drop` is an *unconditional* teardown (per-element decs + data
//! buffer free + struct dealloc). Calling `vec_drop` directly — which is what
//! the S116 foundation's arm did, latent because the arm had no consumer — frees
//! a SHARED Vec on every release.
//!
//! These cells run the generated glue for real. The observable is the ELEMENT's
//! reference count: a `(Vec String)` whose single element is also referenced
//! from outside the vector. Releasing a shared vector (`old_rc > 1`) must touch
//! neither the element nor the buffer; releasing the last reference
//! (`old_rc == 1`) must discharge exactly one element reference.
//!
//! **Falsification (RED-first, the W2b 0885 pattern).** Both cells were run
//! against the broken form — the `GlueShape::Vec` arm restored to a direct
//! `builder.ins().call(vec_drop_ref, &[value, child_ptr])` with no rc dec and no
//! `old_rc == 1` branch:
//!
//! * `a_shared_vec_release_frees_nothing_neg` FAILED —
//!   `element rc after releasing a SHARED vector: … left: 1, right: 2`: the
//!   unconditional `vec_drop` walked the elements and freed the buffer + struct
//!   of a vector still reachable from another owner.
//! * `the_last_reference_release_discharges_the_element` still PASSED, which is
//!   the point of keeping it: it is the control that stops the RED being curable
//!   by emitting nothing. Against a second broken form — an EMPTY arm — the
//!   polarity flips: the control fails at
//!   `element rc after the FINAL release: left 2, right 1`, and the negative
//!   fails on its decrement assertion (`a shared release is a DECREMENT:
//!   left 2, right 1`) while its element assertion passes.

use dashmap::DashMap;

use cranelisp_types::{
    ConcreteType, FQTypeName, HeapHeader, ModuleFullPath, SymbolTable, TypeName,
};

use super::DropGlueRegistry;

/// `(Vec String)` — the smallest owning vector whose per-element release is
/// observable from outside the vector.
fn vec_of_string() -> ConcreteType {
    ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
        vec![ConcreteType::String],
    )
}

/// Build the canonical `(Vec String)` glue through the registry into a JIT
/// module, finalize, and return the JIT (which owns the code pages) plus the
/// glue body's entry address.
fn jit_vec_string_glue() -> (crate::jit::Jit, usize) {
    let module_path = ModuleFullPath::from("user");
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    tables.insert(module_path.clone(), SymbolTable::new(module_path.clone()));

    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let address = {
        let module = jit.jit_module();
        let ids = crate::jit::declare_intrinsics_generic(module).expect("declare intrinsics");
        let mut registry = DropGlueRegistry::new(
            module_path.clone(),
            ids.dealloc.expect("runtime/dealloc declared"),
            ids.vec_drop,
        );
        registry
            .request_if_owning(module, &tables, vec_of_string())
            .expect("(Vec String) glue request")
            .expect("(Vec String) owns heap, so it has glue");
        let glue_ids = registry.finish().expect("every entry reached Defined");

        use crate::CodeFinalizer;
        module.finalize_for_code_read().expect("finalize");
        let artifacts = crate::project_drop_glues(&*module, glue_ids);
        artifacts
            .get(&vec_of_string())
            .expect("the requested key is projected")
            .jit_address
            .expect("a JIT-finalized glue body has an address")
    };
    (jit, address)
}

/// Read a heap value's reference count (`HeapHeader::RC_OFFSET`).
///
/// SAFETY: `ptr` must name a live heap allocation carrying a `HeapHeader`.
unsafe fn rc_of(ptr: i64) -> i64 {
    unsafe { *((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const i64) }
}

/// Overwrite a heap value's reference count — how a test stands in for "another
/// owner holds a reference".
///
/// SAFETY: as [`rc_of`].
unsafe fn set_rc(ptr: i64, value: i64) {
    unsafe { *((ptr as *mut u8).add(HeapHeader::RC_OFFSET as usize) as *mut i64) = value }
}

/// A one-element `(Vec String)` whose element is ALSO referenced from outside
/// the vector (element rc = 2). Returns `(vec, element)`.
fn shared_element_vec() -> (i64, i64) {
    let element = cranelisp_intrinsics::heap_string::heap_alloc_string(b"hi".as_ptr(), 2);
    let vec = cranelisp_intrinsics::vec_runtime::vec_new(1);
    let vec = cranelisp_intrinsics::vec_runtime::vec_push_grow(vec, element);
    // The push TRANSFERS the caller's reference into the vector; the second
    // reference is the simulated outside owner whose survival the cells read.
    // SAFETY: `element` is the `heap_alloc_string` allocation minted three lines
    // above — a live `HeapHeader`-carrying heap value. `vec_push_grow` stored it
    // into the vector without releasing it (the transfer noted above), so nothing
    // between the allocation and here can have freed it. `set_rc`'s contract
    // ("a live heap allocation carrying a `HeapHeader`") is discharged.
    unsafe { set_rc(element, 2) };
    (vec, element)
}

/// Call the generated glue body (`(i64) -> ()`).
///
/// SAFETY: `address` must be the finalized entry of a glue body still owned by a
/// live `Jit`, and `value` a heap pointer of that body's concrete type.
unsafe fn call_glue(address: usize, value: i64) {
    let f: extern "C" fn(i64) = unsafe { std::mem::transmute(address) };
    f(value)
}

// spec: appendix-c-nfr §C.1.4 (NEGATIVE — `transitive-drop-glue.md` §10 row 3,
// "no field call on `old_rc > 1`") — releasing a SHARED `(Vec String)` through
// the canonical glue decrements and stops. No element release, no buffer free,
// no struct dealloc: another owner is still reachable through the same pointer.
//
// This is the cell the unconditional-`vec_drop` arm fails. It is the arm's only
// unsafe direction — the leak direction is loud but survivable; this one hands
// the surviving owner a freed buffer.
#[test]
fn a_shared_vec_release_frees_nothing_neg() {
    let (_jit, glue) = jit_vec_string_glue();
    let (vec, element) = shared_element_vec();
    // A second owner of the VECTOR — the shape whose teardown must not happen.
    // SAFETY: `vec` is the `vec_new`/`vec_push_grow` allocation `shared_element_vec`
    // just returned — a live `HeapHeader`-carrying heap value, not yet released by
    // anything in this frame.
    unsafe { set_rc(vec, 2) };

    // SAFETY: `glue` is the `jit_address` of the finalized `(Vec String)` glue body
    // projected on the line above's `jit_vec_string_glue`, and `_jit` — the `Jit`
    // that owns those code pages — is bound for the whole test body, so the address
    // stays mapped across this call. `vec` is the live `(Vec String)` allocation
    // that body's concrete type names, and generated glue bodies are `(i64) -> ()`,
    // matching the `extern "C" fn(i64)` the transmute produces.
    unsafe { call_glue(glue, vec) };

    assert_eq!(
        // SAFETY: `element` is kept live across the release by the simulated outside
        // owner's reference (rc raised to 2 in `shared_element_vec`); the release
        // just made took the SHARED path, which by the contract under test touches
        // neither the elements nor the buffer. Reading that rc is the observation
        // this cell exists to make — against the broken unconditional-`vec_drop`
        // arm it is precisely the freed-out-from-under-the-owner read the module
        // header's falsification run reports.
        unsafe { rc_of(element) },
        2,
        "element rc after releasing a SHARED vector: the `old_rc > 1` path must \
         not reach the elements. An unconditional `runtime/vec_drop` walks every \
         element, frees the data buffer and deallocs the struct — out from under \
         the owner still holding the other reference."
    );
    assert_eq!(
        // SAFETY: `vec` was allocated with rc 1, raised to 2 above, and the release
        // just made was a decrement — so the struct is still a live
        // `HeapHeader`-carrying allocation held by the remaining reference. That it
        // holds exactly 1 is what the assertion checks.
        unsafe { rc_of(vec) },
        1,
        "a shared release is a DECREMENT: the vector must survive with one \
         reference left."
    );
    // The struct and buffer are still live and consistent.
    assert_eq!(crate::test_support::vec_len_for_test(vec), 1);

    // Clean up the fixture through the same (now sole-owner) path.
    // SAFETY: same discharge as the first `call_glue` — `_jit` still owns the
    // finalized code at `glue` (it is bound until the end of this fn), and `vec` is
    // still the live `(Vec String)` allocation, its rc asserted to be 1 immediately
    // above. This is therefore the sole-owner teardown, and no later statement in
    // this fn reads `vec` or `element`.
    unsafe { call_glue(glue, vec) };
}

// spec: appendix-c-nfr §C.1.4 — the positive half of §10 row 3: on the LAST
// reference (`old_rc == 1`) the canonical glue does discharge the vector, and
// its per-element adapter releases exactly one element reference each.
//
// Kept beside the negative deliberately: it is the control that stops the
// negative from being satisfiable by an arm that releases nothing at all.
#[test]
fn the_last_reference_release_discharges_the_element() {
    let (_jit, glue) = jit_vec_string_glue();
    let (vec, element) = shared_element_vec();
    // Sole owner of the vector; the element still has an outside reference, so
    // reading its rc after the teardown is defined.
    // SAFETY: `vec` is the live `HeapHeader`-carrying allocation `shared_element_vec`
    // returned on the line above; nothing has released it yet.
    assert_eq!(unsafe { rc_of(vec) }, 1);

    // SAFETY: `glue` is the `jit_address` of the finalized `(Vec String)` glue body,
    // and `_jit` — owner of those code pages — is bound for the whole test body, so
    // the address stays mapped across the call. `vec` is the live `(Vec String)`
    // allocation that body's concrete type names, and the body is `(i64) -> ()`,
    // matching the `extern "C" fn(i64)` the transmute produces. Its rc is 1
    // (asserted above), so this is the sole-owner teardown and `vec` is dead after.
    unsafe { call_glue(glue, vec) };

    assert_eq!(
        // SAFETY: `element` survives the teardown just made because
        // `shared_element_vec` gave it a second, outside-owner reference; the
        // teardown discharges only the vector's own. So the allocation is still
        // live and `HeapHeader`-carrying, and reading its rc — the point of the
        // cell — is defined. `vec` is NOT read again after its release.
        unsafe { rc_of(element) },
        1,
        "element rc after the FINAL release: the `old_rc == 1` branch must run \
         the per-element adapter exactly once. A glue arm that decrements but \
         never tears down leaks the element, the data buffer and the struct."
    );
}
