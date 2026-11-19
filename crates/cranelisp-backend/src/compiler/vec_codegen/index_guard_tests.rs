//! ACT-1037 — the one Vec index guard on every `vec-set` lowering
//! (`design/backend/s122-closure.md` §9.3, `backend.md` §7).
//!
//! Each probe is a real JIT function over the production runtime: the guard
//! and the `vec-set` core, called on a Vec the test
//! builds with the intrinsics' own constructors. An out-of-range index must
//! raise the spec §12.7.2.1 panic before any element load, element release,
//! uniqueness probe or `vec-set-copy` call. The raise ends the process, so the
//! out-of-range cells run the probe in a child (`crate::test_child`).

use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_intrinsics::vec_runtime::{vec_new, vec_push_grow};
use cranelisp_types::{
    ConcreteType, FQTypeName, HeapHeader, ModuleFullPath, Span, SymbolTable, TypeName,
};
use dashmap::DashMap;

use super::{
    OwnedSource, VecSetCow, elem_release_fn_ptr, emit_vec_get_core, emit_vec_set_cow_core,
};
use crate::jit::{Jit, declare_intrinsics_generic};
use crate::test_child;
use crate::test_support::{assert_raise_terminates, clif_blocks, clif_func_ref};
use crate::test_support::{vec_elem_for_test, vec_len_for_test};

/// The spec §12.7.2.1 message.
const BOUNDS_MESSAGE: &str = "vec-get: index out of bounds";

/// Negative, equal to the length of a three-element Vec, and far past it.
const OUT_OF_RANGE: [i64; 3] = [-1, 3, 100_000_000];

/// The `vec-set` lowering: the source is always owned and the dynamic rc
/// probe chooses in place or copy (`uniform-counting.md` §2, rule U2).
#[derive(Clone, Copy, Debug)]
enum Case {
    Dynamic,
}

const CASES: [Case; 1] = [Case::Dynamic];

#[derive(Clone, Copy, PartialEq, Eq)]
enum Elem {
    Int,
    String,
    /// `(Vec String)`: an element that owns a heap graph.
    StringVec,
}

impl Elem {
    fn concrete(self) -> ConcreteType {
        match self {
            Elem::Int => ConcreteType::Int,
            Elem::String => ConcreteType::String,
            Elem::StringVec => ConcreteType::ADT(
                FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
                vec![ConcreteType::String],
            ),
        }
    }
}

struct Probe {
    jit: Jit,
    func: FuncId,
    clif: String,
    panic: FuncId,
}

/// Build and finalize `probe(vec, idx, val) -> Vec`: the `vec-set` lowering
/// for `case` over an owned source. Elements are scalars (`Int`),
/// always-heap (`String`) or owning (`(Vec String)`), each released through
/// the registry's canonical adapter; a heap element's retained copies are
/// never incremented because the probes that use it never take the copy arm.
fn build_probe(case: Case, elem: Elem) -> Probe {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let ids = declare_intrinsics_generic(module).expect("declare intrinsics");
    let panic = ids.panic.expect("runtime/panic");
    let vec_drop = ids.vec_drop.expect("runtime/vec_drop");
    let module_path = ModuleFullPath::from("user");
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    tables.insert(module_path.clone(), SymbolTable::new(module_path.clone()));
    let mut registry = crate::test_support::probe_glue_registry(module_path, &ids);
    let elem_release = registry
        .request_vec_elem_adapter(module, &tables, &elem.concrete(), Span::SYNTHETIC)
        .expect("element release adapter");

    let mut sig = module.make_signature();
    for _ in 0..3 {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));
    let func = module
        .declare_function("index_guard_probe", Linkage::Export, &sig)
        .expect("declare probe");

    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut fctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let params = builder.block_params(entry).to_vec();
        let (vec_val, idx_val, new_val) = (params[0], params[1], params[2]);
        let inc_fn_ptr = builder.ins().iconst(types::I64, 0);
        let elem_dec_fn_ptr = elem_release_fn_ptr(&mut builder, module, elem_release);
        let Case::Dynamic = case;
        let source = OwnedSource {
            vec_drop_func_id: vec_drop,
            elem_release,
            elem_dec_fn_ptr,
        };
        let result = emit_vec_set_cow_core(
            &mut builder,
            module,
            VecSetCow {
                vec_val,
                idx_val,
                new_val,
                inc_fn_ptr,
                panic,
                source,
            },
            Span::SYNTHETIC,
        )
        .expect("emit vec-set lowering");
        builder.ins().return_(&[result]);
        builder.seal_all_blocks();
        builder.finalize();
    }
    let clif = ctx.func.display().to_string();
    module
        .define_function(func, &mut ctx)
        .expect("define probe");
    module.clear_context(&mut ctx);
    registry.finish().expect("every glue entry reached Defined");
    jit.finalize().expect("finalize probe");
    Probe {
        jit,
        func,
        clif,
        panic: panic.func_id(),
    }
}

impl Probe {
    /// Call the probe. An out-of-range index ends the process.
    fn call(&mut self, vec: i64, idx: i64, val: i64) -> i64 {
        let code = self.jit.get_finalized_ptr(self.func);
        let f: extern "C" fn(i64, i64, i64) -> i64 = unsafe { std::mem::transmute(code) };
        f(vec, idx, val)
    }
}

fn int_vec(elems: &[i64]) -> i64 {
    elems.iter().fold(vec_new(0), |v, &e| vec_push_grow(v, e))
}

fn string(text: &str) -> i64 {
    cranelisp_intrinsics::heap_string::alloc_string(text.as_bytes()) as i64
}

/// Read a heap value's reference count (`HeapHeader::RC_OFFSET`).
///
/// SAFETY: `ptr` must name a live heap allocation carrying a `HeapHeader`.
unsafe fn rc_of(ptr: i64) -> i64 {
    unsafe { *((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const i64) }
}

fn string_vec(elems: &[&str]) -> i64 {
    elems
        .iter()
        .fold(vec_new(0), |v, e| vec_push_grow(v, string(e)))
}

/// A fresh `[10 20 30]`, shared when `shared` asks for the copy arm.
fn source_for(shared: bool) -> i64 {
    let v = int_vec(&[10, 20, 30]);
    if shared {
        cranelisp_intrinsics::rc::rc_inc(v);
    }
    v
}

const CHILD: &str = "child_calls_probe";

// Child body: call the probe for `CASE` (an index into `CASES`), `ELEM`
// (0 Int, 1 String), `SHARED` and `IDX`.
#[test]
fn child_calls_probe() {
    if !test_child::selected(CHILD) {
        return;
    }
    let case = CASES[test_child::arg::<usize>("CASE")];
    let idx: i64 = test_child::arg("IDX");
    let mut probe = if test_child::arg::<usize>("ELEM") == 0 {
        build_probe(case, Elem::Int)
    } else {
        build_probe(case, Elem::String)
    };
    if test_child::arg::<usize>("ELEM") == 0 {
        probe.call(source_for(test_child::arg("SHARED")), idx, 99);
    } else {
        probe.call(string_vec(&["a", "b", "c"]), idx, string("z"));
    }
    println!("{}", test_child::RESUMED);
}

/// Run the probe in a child at every out-of-range index and assert each run
/// ends by the bounds panic.
fn assert_panics_out_of_range(case: usize, elem: usize, shared: bool, what: &str) {
    let path = test_child::child_path(module_path!(), CHILD);
    for idx in OUT_OF_RANGE {
        let env = [
            ("CASE", case.to_string()),
            ("ELEM", elem.to_string()),
            ("SHARED", shared.to_string()),
            ("IDX", idx.to_string()),
        ];
        test_child::run(&path, &env)
            .assert_panicked_with(BOUNDS_MESSAGE, &format!("{what} at index {idx}"));
    }
}

// spec: spec/12-runtime.md §12.7.2.1 — the `vec-set` lowering panics on a negative index, on index = length and far past it.
#[test]
fn every_vec_set_case_panics_out_of_range() {
    for (i, case) in CASES.iter().enumerate() {
        assert_panics_out_of_range(i, 0, false, &format!("{case:?}"));
    }
}

// spec: spec/12-runtime.md §12.7.2.1 (NEGATIVE) — the child harness tells a
// raise from a return: the same child at an in-range index exits 0, reports no
// panic and prints the resumed marker.
#[test]
fn in_range_child_resumes_without_a_report_neg() {
    let path = test_child::child_path(module_path!(), CHILD);
    let env = [
        ("CASE", "0".to_string()),
        ("ELEM", "0".to_string()),
        ("SHARED", "false".to_string()),
        ("IDX", "2".to_string()),
    ];
    let end = test_child::run(&path, &env);
    assert_eq!(end.code, Some(0), "{}", end.stderr);
    assert!(end.stdout.contains(test_child::RESUMED), "{}", end.stdout);
    assert!(
        !end.stderr
            .contains(cranelisp_intrinsics::panic::PANIC_REPORT_PREFIX),
        "{}",
        end.stderr
    );
}

// spec: spec/12-runtime.md §12.7.2.1 — the dynamic case panics on its copy arm
// too: a shared source reaches `vec-set-copy` only in range.
#[test]
fn dynamic_vec_set_on_a_shared_source_panics_out_of_range() {
    assert_panics_out_of_range(0, 0, true, "dynamic, shared");
}

// spec: spec/12-runtime.md §12.7.2.1 (NEGATIVE) — an in-range index is not a
// panic source in any case: the result holds the new element and keeps the
// others.
#[test]
fn every_vec_set_case_writes_in_range_without_panic_neg() {
    for (case, shared) in [(Case::Dynamic, false), (Case::Dynamic, true)] {
        let mut probe = build_probe(case, Elem::Int);
        let result = probe.call(source_for(shared), 2, 99);
        assert_eq!(vec_len_for_test(result), 3, "{case:?}: length kept");
        assert_eq!(
            vec_elem_for_test(result, 2),
            99,
            "{case:?}: element written"
        );
        assert_eq!(vec_elem_for_test(result, 0), 10, "{case:?}: element kept");
    }
}

// spec: spec/12-runtime.md §12.7.2.1 — heap elements: the in-place arm's
// old-element release is the unsafe step, so the guard must precede it.
#[test]
fn in_place_vec_set_on_string_elements_panics_out_of_range() {
    assert_panics_out_of_range(0, 1, false, "Dynamic, String elements");
}

// spec: spec/12-runtime.md §12.7.2.1 (NEGATIVE) — an in-range String write
// releases the old element once, stores the new one, and leaves the other
// elements' counts alone.
#[test]
fn in_place_vec_set_on_string_elements_writes_in_range_neg() {
    for case in CASES {
        let mut probe = build_probe(case, Elem::String);
        let source = string_vec(&["a", "b", "c"]);
        let (kept, old) = (vec_elem_for_test(source, 0), vec_elem_for_test(source, 1));
        // The test's own reference keeps the old element live, so its release
        // shows as a count of one rather than a free.
        cranelisp_intrinsics::rc::rc_inc(old);
        let new = string("z");
        let result = probe.call(source, 1, new);
        assert_eq!(
            vec_elem_for_test(result, 1),
            new,
            "{case:?}: new String stored"
        );
        // SAFETY: `old` is live on the test's reference; `kept` and `new` are
        // held by `result`.
        let (old_rc, kept_rc, new_rc) = unsafe { (rc_of(old), rc_of(kept), rc_of(new)) };
        assert_eq!(old_rc, 1, "{case:?}: old String released exactly once");
        assert_eq!(kept_rc, 1, "{case:?}: untouched element keeps its count");
        assert_eq!(
            new_rc, 1,
            "{case:?}: new String's reference moves in unretained"
        );
    }
}

/// A one-element `(Vec String)` holding a fresh String. Returns `(vec, string)`.
fn one_string_vec(text: &str) -> (i64, i64) {
    let s = string(text);
    (vec_push_grow(vec_new(0), s), s)
}

// spec: design/backend/uniform-counting.md §3.4 item 5 — the in-place arm
// releases an overwritten element that owns a heap graph through the element
// type's canonical glue, so the last reference to `["old"]` discharges "old".
// S123 U-11 (review R1): a bare decrement freed the inner Vec's box and
// stranded its String, which this cell observed as "old" left at count 2.
#[test]
fn in_place_vec_set_releases_an_owning_old_element_through_its_glue() {
    let mut probe = build_probe(Case::Dynamic, Elem::StringVec);
    let (old_inner, old_string) = one_string_vec("old");
    let source = vec_push_grow(vec_new(0), old_inner);
    // The test's own reference keeps "old" observable after the teardown.
    cranelisp_intrinsics::rc::rc_inc(old_string);
    let (new_inner, _) = one_string_vec("new");
    let result = probe.call(source, 0, new_inner);
    assert_eq!(result, source, "a uniquely held source updates in place");
    assert_eq!(
        vec_elem_for_test(result, 0),
        new_inner,
        "new element stored"
    );
    // SAFETY: `old_string` is live on the test's reference.
    let old_rc = unsafe { rc_of(old_string) };
    assert_eq!(
        old_rc, 1,
        "the old inner Vec's teardown must release its String exactly once"
    );
}

// spec: design/backend/uniform-counting.md §3.4 item 5 (NEGATIVE) — an
// overwritten element that is still shared is decremented, not torn down: its
// contents keep their count and the element stays live for its other owner.
#[test]
fn in_place_vec_set_keeps_a_shared_old_element_live_neg() {
    let mut probe = build_probe(Case::Dynamic, Elem::StringVec);
    let (old_inner, old_string) = one_string_vec("old");
    let source = vec_push_grow(vec_new(0), old_inner);
    // A second owner of the old inner Vec.
    cranelisp_intrinsics::rc::rc_inc(old_inner);
    let (new_inner, _) = one_string_vec("new");
    probe.call(source, 0, new_inner);
    // SAFETY: `old_inner` is live on the second owner's reference, and it
    // holds `old_string`.
    let (inner_rc, string_rc) = unsafe { (rc_of(old_inner), rc_of(old_string)) };
    assert_eq!(inner_rc, 1, "the shared old element loses one reference");
    assert_eq!(string_rc, 1, "its contents are untouched");
    assert_eq!(vec_len_for_test(old_inner), 1, "and still readable");
}

// ---------------------------------------------------------------------------
// Structure: the guard opens the lowering in every case.
// ---------------------------------------------------------------------------

/// Assert the guard shape: the entry block loads the length, compares the
/// index below zero and at or above it, and branches to a block that raises.
/// The entry block performs no call and no store, so the element write and
/// every helper call sit behind the guard.
fn assert_guard_opens(clif: &str, panic: FuncId, what: &str) {
    let blocks = clif_blocks(clif);
    let (_, entry) = &blocks[0];
    let has = |needle: &str| entry.iter().any(|l| l.contains(needle));
    assert!(
        has("load.i64") && has("icmp slt") && has("icmp sge") && has("bor"),
        "{what}: the entry block must compare the index with zero and the loaded \
         length\n{clif}"
    );
    assert!(
        !entry
            .iter()
            .any(|l| l.contains("call ") || l.contains("store.")),
        "{what}: nothing may call or store before the guard branches\n{clif}"
    );
    let brif = entry.last().expect("entry terminator");
    let taken = brif
        .strip_prefix("brif ")
        .and_then(|rest| rest.split(", ").nth(1))
        .map(|t| t.split('(').next().unwrap_or(t).to_string())
        .unwrap_or_else(|| panic!("{what}: the entry block must end in the guard's brif\n{clif}"));
    let panic_ref = clif_func_ref(clif, panic);
    let (_, panic_block) = blocks
        .iter()
        .find(|(label, _)| *label == taken)
        .expect("taken block");
    assert!(
        panic_block
            .iter()
            .any(|l| l.contains(&format!("call {panic_ref}("))),
        "{what}: the guard's taken arm must call runtime/panic\n{clif}"
    );
    assert_raise_terminates(clif, panic, what);
}

// spec: design/backend/backend.md §7 "One Vec index guard" — the guard
// precedes the element store and the `vec-set-copy` call.
#[test]
fn guard_opens_every_vec_set_case() {
    for case in CASES {
        let probe = build_probe(case, Elem::String);
        assert_guard_opens(&probe.clif, probe.panic, &format!("{case:?}"));
    }
}

// spec: design/backend/uniform-counting.md §2 (rule U2) — the lowering keeps
// the rc probe and both arms: in place at count 1, a copy call otherwise.
#[test]
fn the_vec_set_lowering_probes_and_keeps_both_arms() {
    let probe = build_probe(Case::Dynamic, Elem::Int);
    let panic_call = format!("call {}(", clif_func_ref(&probe.clif, probe.panic));
    let helper_calls = probe
        .clif
        .lines()
        .filter(|l| l.contains("call ") && !l.contains(&panic_call))
        .count();
    assert!(
        probe.clif.contains("icmp eq") && probe.clif.contains("store.") && helper_calls >= 1,
        "{}",
        probe.clif
    );
}

// ---------------------------------------------------------------------------
// vec-get: the extraction leaves its emission unchanged.
// ---------------------------------------------------------------------------

/// `vec-get` over String elements in a module that declares only
/// `runtime/panic`, so the rendered function references stay stable.
fn vec_get_clif() -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let panic = crate::raise::PanicHandle::declare_alone(module);
    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let (vec_val, idx_val) = (
        builder.block_params(entry)[0],
        builder.block_params(entry)[1],
    );
    let elem = emit_vec_get_core(
        &mut builder,
        module,
        panic,
        crate::heap::HeapCategory::AlwaysHeap,
        vec_val,
        idx_val,
        Span::SYNTHETIC,
    )
    .expect("emit vec-get");
    builder.ins().return_(&[elem]);
    builder.finalize();
    ctx.func.display().to_string()
}

/// A whole-function byte pin of `vec_get_clif()`, first taken from the tree
/// before ACT-1037 shared the guard with `vec-set`. It covers more than the
/// guard: the element load and the element retain are pinned too, so any
/// intended change to `vec-get` emission re-baselines it. Last re-baselined
/// when the raise became a call and a trap (S123).
const VEC_GET_CLIF: &str = r#"function u0:0(i64, i64) -> i64 system_v {
    gv0 = symbol colocated userextname0
    sig0 = (i64, i64) system_v
    fn0 = u0:0 sig0

block0(v0: i64, v1: i64):
    v2 = load.i64 notrap aligned v0+16
    v3 = iconst.i64 0
    v4 = icmp slt v1, v3  ; v3 = 0
    v5 = icmp sge v1, v2
    v6 = bor v4, v5
    brif v6, block2, block1

block2:
    v7 = global_value.i64 gv0
    v8 = iconst.i64 28
    call fn0(v7, v8)  ; v8 = 28
    trap user1

block1:
    v9 = load.i64 notrap aligned v0+32
    v10 = iconst.i64 8
    v11 = imul.i64 v1, v10  ; v10 = 8
    v12 = iadd v9, v11
    v13 = load.i64 notrap aligned v12
    v14 = iadd_imm v13, 8
    v15 = iconst.i64 1
    v16 = atomic_rmw.i64 add v14, v15  ; v15 = 1
    return v13
}
"#;

// spec: design/backend/s122-closure.md §9.2 (NEGATIVE) — sharing the guard
// leaves vec-get's emitted instructions byte-identical.
#[test]
fn vec_get_emission_is_unchanged_by_the_shared_guard_neg() {
    assert_eq!(vec_get_clif(), VEC_GET_CLIF);
}
