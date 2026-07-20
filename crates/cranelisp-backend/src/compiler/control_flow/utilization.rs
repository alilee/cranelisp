// Utilization-model measurement instrumentation (Sprint 104 Wave 0).
//
// This is the **measurement half** of the M-static quality axis
// (`design/backend/lenient-eval.md` §2.8.2). Wave 0 computes the M-static
// classification `{recursive-SCC?, tail?}` at every current spark site and
// records it into a gated registry (`CRANELISP_SPARK_STATS=1`) WITHOUT changing
// whether the site sparks — the discrimination-experiment substrate for `/qa`'s
// Stage-0 measurement (`tests/plan/s104-utilization-measurement.md` §4). The
// classifier itself (recursive-SCC membership + the admit predicate) is the pure
// function M-static (Wave 1) will consume to *act* on the decision; here it is
// only observed.
//
// Zero-cost when off: every recording entry point reads a single `LazyLock` bool
// (`spark_stats_enabled`) and returns before building the call graph or taking
// any lock, so a normal (`CRANELISP_SPARK_STATS` unset) compile pays one bool
// load per spark site and nothing else.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;
use std::sync::{LazyLock, Mutex};

use cranelift_module::Module;

use cranelisp_types::{FQSymbol, ModuleEntry, ModuleFullPath, MonoExpr, Span, Symbol};

use super::FnCompiler;

// ── The pure classifier (M-static quality axis, §2.8.2) ──────────────────────

/// Recursive-SCC membership over the static call graph.
///
/// Given the directed call graph (nodes = FQ callables, edges = `callees`),
/// returns the set of nodes that belong to a **recursive** SCC: an SCC with
/// more than one node (mutual recursion) OR a node carrying a self-edge (direct
/// self-recursion — a singleton SCC with a self-loop). Plain Tarjan SCC over the
/// node set = every key plus every callee that appears as an edge target.
///
/// **NOTE (S104 Wave 0).** The `callees` feed **skips self-edges** (the
/// recursion name is shadowed by the local binding at check time — typecheck
/// §"Def.callees completeness contract"), so *direct* self-recursion does NOT
/// reach this function through the graph. This function still classifies a
/// present self-edge correctly (for the unit-test matrix and for any future feed
/// that carries them); at the spark site direct self-recursion is recovered
/// separately by the per-site self-call check in [`FnCompiler::classify_spark_callee`].
pub(crate) fn recursive_scc_members(
    graph: &HashMap<FQSymbol, Vec<FQSymbol>>,
) -> HashSet<FQSymbol> {
    // Collect the node universe: callers + every referenced callee.
    let mut nodes: Vec<FQSymbol> = Vec::new();
    let mut index_of: HashMap<FQSymbol, usize> = HashMap::new();
    let intern = |n: &FQSymbol, nodes: &mut Vec<FQSymbol>, index_of: &mut HashMap<FQSymbol, usize>| -> usize {
        if let Some(&i) = index_of.get(n) {
            i
        } else {
            let i = nodes.len();
            nodes.push(n.clone());
            index_of.insert(n.clone(), i);
            i
        }
    };
    for (caller, callees) in graph {
        intern(caller, &mut nodes, &mut index_of);
        for callee in callees {
            intern(callee, &mut nodes, &mut index_of);
        }
    }

    // Adjacency by interned index. Track self-edges separately — a singleton SCC
    // with a self-edge is recursive even though Tarjan groups it alone.
    let n = nodes.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut has_self_edge: Vec<bool> = vec![false; n];
    for (caller, callees) in graph {
        let ci = index_of[caller];
        for callee in callees {
            let ki = index_of[callee];
            if ki == ci {
                has_self_edge[ci] = true;
            }
            adj[ci].push(ki);
        }
    }

    // Iterative Tarjan (recursion-free — the call graph can be deep).
    let mut idx: Vec<Option<u32>> = vec![None; n];
    let mut low: Vec<u32> = vec![0; n];
    let mut on_stack: Vec<bool> = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index: u32 = 0;
    let mut recursive: HashSet<FQSymbol> = HashSet::new();

    // Explicit DFS frame: (node, next-adjacency-cursor).
    for start in 0..n {
        if idx[start].is_some() {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&(v, ci)) = work.last() {
            if ci == 0 {
                idx[v] = Some(next_index);
                low[v] = next_index;
                next_index += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if ci < adj[v].len() {
                let w = adj[v][ci];
                work.last_mut().unwrap().1 += 1;
                match idx[w] {
                    None => work.push((w, 0)),
                    Some(_) if on_stack[w] => low[v] = low[v].min(idx[w].unwrap()),
                    Some(_) => {}
                }
            } else {
                // Done with v's edges — settle its low-link into its parent.
                if low[v] == idx[v].unwrap() {
                    // Root of an SCC — pop it and mark recursion.
                    let mut members: Vec<usize> = Vec::new();
                    loop {
                        let w = stack.pop().unwrap();
                        on_stack[w] = false;
                        members.push(w);
                        if w == v {
                            break;
                        }
                    }
                    let is_recursive = members.len() > 1 || has_self_edge[v];
                    if is_recursive {
                        for &m in &members {
                            recursive.insert(nodes[m].clone());
                        }
                    }
                }
                work.pop();
                if let Some(&(p, _)) = work.last() {
                    low[p] = low[p].min(low[v]);
                }
            }
        }
    }

    recursive
}

/// The M-static admission predicate (`lenient-eval.md` §2.8.2): a candidate is
/// sparkable iff its callee is in a recursive SCC **and** the apply is not in
/// tail position. QUALITY axis only. **Wave 0 computes this for measurement; it
/// does NOT yet gate whether the site sparks (that is Wave 1's M-static build).**
pub(crate) fn mstatic_admits(callee_in_recursive_scc: bool, in_tail_position: bool) -> bool {
    callee_in_recursive_scc && !in_tail_position
}

// ── Bare-name normalisation (mono/sig-suffix + module-prefix stripping) ──────

/// The source-level bare symbol of a possibly-qualified, possibly-mono-mangled
/// name: strip a leading `module/` qualifier and a trailing `$…` monomorphisation
/// / sig-dispatch suffix (`fib$Int` → `fib`, `mod/reduce-tree$Int` → `reduce-tree`).
fn bare_name(s: &str) -> &str {
    let after_module = s.rsplit('/').next().unwrap_or(s);
    after_module.split('$').next().unwrap_or(after_module)
}

/// The graph-node `FQSymbol` for a callee reference `name` seen in `current`
/// module context: split a `module/symbol` qualifier if present, else assume the
/// current module; the symbol is normalised to its source bare name so it matches
/// the `callees`-derived graph keys.
fn callee_fqsymbol(current: &ModuleFullPath, name: &str) -> FQSymbol {
    if let Some(pos) = name.find('/') {
        FQSymbol {
            module: ModuleFullPath::from(&name[..pos]),
            symbol: Symbol::from(bare_name(&name[pos + 1..])),
        }
    } else {
        FQSymbol {
            module: current.clone(),
            symbol: Symbol::from(bare_name(name)),
        }
    }
}

// ── The gated SPARK_SITE_STATS registry (compile-time) ───────────────────────

fn spark_stats_enabled() -> bool {
    static E: LazyLock<bool> = LazyLock::new(|| {
        let on = std::env::var_os("CRANELISP_SPARK_STATS").is_some();
        if on {
            SITE_STATS_ATEXIT.call_once(|| unsafe {
                libc::atexit(dump_site_stats);
            });
        }
        on
    });
    *E
}

static SITE_STATS_ATEXIT: std::sync::Once = std::sync::Once::new();

/// One recorded spark site: its M-static classification plus the number of
/// monomorphised instantiations that emitted a spark there (`emits`). Runtime
/// spawn *volume* per site is not attributed here — that requires a compile→run
/// channel M-static (Wave 1) introduces; Wave 0 pairs this classification with
/// the aggregate runtime `SPARK_SPAWNS` (ivar.rs) which the harness reads
/// together (`tests/plan/s104-utilization-measurement.md` §3/§4).
struct SiteRecord {
    scc: bool,
    tail: bool,
    /// The M-static verdict `mstatic_admits(scc, tail)` — the would-spark
    /// decision M-static (Wave 1) will act on. Recorded here so the harness
    /// reads the classification's *outcome* directly, not just its inputs.
    admit: bool,
    emits: u64,
}

/// site-id (`callee-FQ@start..end`) → record. `BTreeMap` for a stable, sorted
/// dump order.
static SITE_STATS: LazyLock<Mutex<BTreeMap<String, SiteRecord>>> =
    LazyLock::new(|| Mutex::new(BTreeMap::new()));

fn record_site(callee_fq: &str, span: Span, scc: bool, tail: bool) {
    let site_id = format!("{}@{}..{}", callee_fq, span.start, span.end);
    let mut m = SITE_STATS.lock().unwrap();
    let e = m.entry(site_id).or_insert(SiteRecord {
        scc,
        tail,
        admit: mstatic_admits(scc, tail),
        emits: 0,
    });
    e.emits += 1;
}

extern "C" fn dump_site_stats() {
    let m = SITE_STATS.lock().unwrap();
    for (id, r) in m.iter() {
        eprintln!(
            "[SPARK_SITE_STATS] site={} scc={} tail={} admit={} emits={}",
            id, r.scc, r.tail, r.admit, r.emits
        );
    }
}

// ── Recording entry points (called from the two spark sites) ─────────────────

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Build the interprocedural call graph from the loaded symbol tables'
    /// `ModuleEntry::Def.callees` (Decision 21, FIXME-0470-enriched). Nodes are
    /// source-level `FQSymbol`s; edges are the recorded callees. Self-edges are
    /// absent (skipped by the `callees` feed — see [`recursive_scc_members`]).
    /// Built fresh per spark site (only when spark-stats is on): compile-time,
    /// gated, and cheap at fixture scale.
    fn build_call_graph(&self) -> HashMap<FQSymbol, Vec<FQSymbol>> {
        let mut graph: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        for table_ref in self.ctx.symbol_tables.iter() {
            let module = table_ref.key().clone();
            for (name, entry) in table_ref.value().symbols.iter() {
                if let ModuleEntry::Def { callees, .. } = entry {
                    let caller = FQSymbol {
                        module: module.clone(),
                        symbol: name.clone(),
                    };
                    graph
                        .entry(caller)
                        .or_default()
                        .extend(callees.iter().cloned());
                }
            }
        }
        graph
    }

    /// Classify one spark candidate (an `Apply`) for the M-static discrimination:
    /// `(callee-fq-string, scc?, tail?, span)`. `scc?` = callee is in a mutual-
    /// recursion SCC (`recursive` set) OR the call is a direct self-call
    /// (callee bare-name == the enclosing function — recovers the self-edge the
    /// `callees` feed drops). `tail?` = the candidate's own tail position
    /// (spark candidates are compiled non-tail, so this is `false` at every
    /// current site — recorded faithfully). Returns `None` for a non-`Apply` or a
    /// computed (non-`Var`) callee ⇒ treated as non-recursive/decline, the
    /// soundness-toward-decline default (§2.8.2).
    fn classify_spark_callee(
        &self,
        candidate: &MonoExpr,
        recursive: &HashSet<FQSymbol>,
    ) -> Option<(String, bool, bool, Span)> {
        let MonoExpr::Apply { callee, span, resolved_call, .. } = candidate else {
            return None;
        };
        let MonoExpr::Var { name, .. } = callee.as_ref() else {
            return None;
        };
        let fq = callee_fqsymbol(&self.ctx.current_module, name);
        // Direct self-recursion recovery (the self-edge the `callees` feed drops).
        // Uses the ONE shared `is_self_call` predicate (FIXME 0654; Principle 7) —
        // the carrier-keyed identity + the `SigDispatch` mangled-name shape — NOT
        // the pre-S113 bare written-name compare (which false-admitted a §4.6-
        // shadowed local named like the fn as self-recursive; the carrier is
        // absent for a local, so `is_self_call` correctly declines). Scheduling-
        // only: a mis-classification is sound (lenient-eval §2.8.2). `fq` (composed
        // from the written name, mono-suffix-stripped) is retained for the SCC-set
        // membership lookup, a separate concern from the self-edge.
        let is_self = crate::compiler::is_self_call(
            callee.as_ref(),
            resolved_call.as_deref(),
            &self.ctx.current_module,
            self.current_fn_name.as_ref(),
        );
        let scc = is_self || recursive.contains(&fq);
        Some((fq.to_string(), scc, false, *span))
    }

    /// The recursive-SCC membership set over the loaded call graph, built once
    /// and cached per `FnCompiler` (`design/backend/lenient-eval.md` §2.8.6 —
    /// "cached per compile unit and read at each candidate site"). M-static
    /// (Wave 1) consults this at *every* spark-eligible `let`/apply site, so the
    /// O(defs) Tarjan pass must not rerun per site. The cache is interior-mutable
    /// (`RefCell`) so it populates lazily on the `&self` admission path; an inner
    /// compiler (lambda / thunk body) has its own fresh cache, which is correct —
    /// the graph is a pure function of the (unchanging) loaded symbol tables, so
    /// a rebuild yields the identical set.
    pub(crate) fn mstatic_recursive_set(&self) -> Rc<HashSet<FQSymbol>> {
        if let Some(set) = self.mstatic_recursive_cache.borrow().as_ref() {
            return set.clone();
        }
        let graph = self.build_call_graph();
        let set = Rc::new(recursive_scc_members(&graph));
        *self.mstatic_recursive_cache.borrow_mut() = Some(set.clone());
        set
    }

    /// The M-static admission verdict for one spark candidate
    /// (`design/backend/lenient-eval.md` §2.8.2) — the `worth` predicate the
    /// `find_sparkable_*_with` cores call in `CRANELISP_SPARK_ADMIT=mstatic`.
    ///
    /// Admits iff [`classify_spark_callee`] resolves the candidate to a callee in
    /// a recursive SCC (incl. direct self-recursion) that is **not** in tail
    /// position — [`mstatic_admits`]. A non-`Apply`, a computed (non-`Var`)
    /// callee, or an unresolved/unloaded callee classifies as `None` ⇒
    /// **decline**: the soundness-toward-decline default (§2.8.2 —
    /// spark-vs-inline is a scheduling choice only, §8, so declining is always
    /// sound). This is a deliberate divergence from the syntactic filter, which
    /// *sparks* a computed callee (unknown cost); M-static declines it because a
    /// HOF/closure indirection is not a resolved recursive SCC.
    pub(crate) fn mstatic_admits_candidate(
        &self,
        candidate: &MonoExpr,
        recursive: &HashSet<FQSymbol>,
    ) -> bool {
        match self.classify_spark_callee(candidate, recursive) {
            Some((_, scc, tail, _)) => mstatic_admits(scc, tail),
            None => false,
        }
    }

    /// Record the M-static classification of every sparkable apply argument at an
    /// apply spark site (`lenient-eval.md` §4.4 / §2.8.6). Measurement-only —
    /// does NOT change admission. Zero-cost when spark-stats is off (early
    /// return before any graph build).
    pub(crate) fn record_spark_sites_apply(&self, args: &[MonoExpr], sparkable: &[usize]) {
        if !spark_stats_enabled() {
            return;
        }
        let graph = self.build_call_graph();
        let recursive = recursive_scc_members(&graph);
        for &idx in sparkable {
            if let Some((fq, scc, tail, span)) =
                self.classify_spark_callee(&args[idx], &recursive)
            {
                record_site(&fq, span, scc, tail);
            }
        }
    }

    /// Record the M-static classification of every sparkable `let` binding RHS at
    /// a `let` spark site (`lenient-eval.md` §4.2 / §2.8.6). Measurement-only.
    /// Zero-cost when spark-stats is off.
    pub(crate) fn record_spark_sites_let(
        &self,
        bindings: &[(Symbol, MonoExpr)],
        sparkable: &[usize],
    ) {
        if !spark_stats_enabled() {
            return;
        }
        let graph = self.build_call_graph();
        let recursive = recursive_scc_members(&graph);
        for &idx in sparkable {
            if let Some((fq, scc, tail, span)) =
                self.classify_spark_callee(&bindings[idx].1, &recursive)
            {
                record_site(&fq, span, scc, tail);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fq(module: &str, symbol: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(symbol),
        }
    }

    // --- recursive_scc_members: the {recursive, non-recursive} graph shapes ---

    #[test]
    fn scc_direct_self_recursion_is_recursive() {
        // fib -> fib (self-edge). A singleton SCC with a self-loop is recursive.
        let mut g: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        g.insert(fq("user", "fib"), vec![fq("user", "fib")]);
        let r = recursive_scc_members(&g);
        assert!(r.contains(&fq("user", "fib")));
    }

    #[test]
    fn scc_mutual_recursion_is_recursive() {
        // a -> b -> a: a two-node recursive SCC.
        let mut g: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        g.insert(fq("user", "a"), vec![fq("user", "b")]);
        g.insert(fq("user", "b"), vec![fq("user", "a")]);
        let r = recursive_scc_members(&g);
        assert!(r.contains(&fq("user", "a")));
        assert!(r.contains(&fq("user", "b")));
    }

    #[test]
    fn scc_flat_call_is_not_recursive() {
        // cell-at is a leaf accessor called by a hot loop — no cycle, no self-edge.
        let mut g: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        g.insert(fq("user", "loop"), vec![fq("user", "cell-at")]);
        g.insert(fq("user", "cell-at"), vec![]);
        let r = recursive_scc_members(&g);
        assert!(!r.contains(&fq("user", "cell-at")));
        assert!(!r.contains(&fq("user", "loop")));
    }

    #[test]
    fn scc_three_node_cycle_all_recursive() {
        // a -> b -> c -> a — a size-3 SCC.
        let mut g: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        g.insert(fq("user", "a"), vec![fq("user", "b")]);
        g.insert(fq("user", "b"), vec![fq("user", "c")]);
        g.insert(fq("user", "c"), vec![fq("user", "a")]);
        let r = recursive_scc_members(&g);
        for n in ["a", "b", "c"] {
            assert!(r.contains(&fq("user", n)), "{n} should be recursive");
        }
    }

    #[test]
    fn scc_recursive_head_with_flat_leaf_separates() {
        // solve-range -> solve-range (D&C, self) AND solve-range -> cell-at (leaf).
        // The self-recursive coarse head is recursive; the flat leaf is not — the
        // exact F4 discrimination the utilization model needs.
        let mut g: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        g.insert(
            fq("user", "solve-range"),
            vec![fq("user", "solve-range"), fq("user", "cell-at")],
        );
        g.insert(fq("user", "cell-at"), vec![]);
        let r = recursive_scc_members(&g);
        assert!(r.contains(&fq("user", "solve-range")), "coarse D&C kept");
        assert!(!r.contains(&fq("user", "cell-at")), "flat leaf rejected");
    }

    #[test]
    fn scc_empty_graph_has_no_recursion() {
        let g: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        assert!(recursive_scc_members(&g).is_empty());
    }

    // --- mstatic_admits: the {recursive, non-recursive} × {tail, non-tail} matrix ---

    #[test]
    fn mstatic_recursive_nontail_admits() {
        // fib / solve-range coarse D&C: recursive, non-tail → SPARK.
        assert!(mstatic_admits(true, false));
    }

    #[test]
    fn mstatic_recursive_tail_declines() {
        // tail-recursive accumulator loop: recursive but tail → decline (TCO jump).
        assert!(!mstatic_admits(true, true));
    }

    #[test]
    fn mstatic_nonrecursive_nontail_declines() {
        // flat cell-at accessor pair: non-recursive, non-tail → decline.
        assert!(!mstatic_admits(false, false));
    }

    #[test]
    fn mstatic_nonrecursive_tail_declines() {
        // flat call in tail position: non-recursive, tail → decline.
        assert!(!mstatic_admits(false, true));
    }

    // --- bare-name normalisation ---

    #[test]
    fn bare_name_strips_module_and_mono_suffix() {
        assert_eq!(bare_name("fib"), "fib");
        assert_eq!(bare_name("fib$Int"), "fib");
        assert_eq!(bare_name("mod/reduce-tree"), "reduce-tree");
        assert_eq!(bare_name("mod/reduce-tree$Int"), "reduce-tree");
    }

    #[test]
    fn callee_fqsymbol_qualified_and_bare() {
        let cur = ModuleFullPath::from("user");
        assert_eq!(callee_fqsymbol(&cur, "fib$Int"), fq("user", "fib"));
        assert_eq!(callee_fqsymbol(&cur, "other/g$Int"), fq("other", "g"));
    }

    // --- M-static admission through the real classifier (Wave 1) ---
    //
    // Drives `classify_spark_callee` / `mstatic_admits_candidate` / the
    // `find_sparkable_args_with` seam through a throwaway `FnCompiler` over a JIT
    // module (the `trace_codegen::tests` harness pattern), so the Task-0
    // module-blind self-call fix and the §2.8.2 admission matrix are exercised on
    // the *actual* codegen methods, not a mirror of their logic.

    fn apply_var(callee: &str, ret: cranelisp_types::ConcreteType) -> MonoExpr {
        apply_var_inner(callee, None, ret)
    }
    /// `apply_var` whose callee `Var` carries a `resolved_target` storage FQ — the
    /// realistic shape the producer records for a resolved reference (the self-
    /// recursion carve-out records `{module, fn}` for a genuine self-call). The
    /// carrier-keyed `is_self_call` predicate keys on THIS, not the written name.
    fn apply_var_c(callee: &str, module: &str, symbol: &str, ret: cranelisp_types::ConcreteType) -> MonoExpr {
        apply_var_inner(callee, Some(fq(module, symbol)), ret)
    }
    fn apply_var_inner(callee: &str, carrier: Option<FQSymbol>, ret: cranelisp_types::ConcreteType) -> MonoExpr {
        MonoExpr::Apply {
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(MonoExpr::Var {
                // S114 flip: a carrier present ⇒ the table-resolved verdict (the
                // fp1 self-call carrier shape); absent ⇒ a scope-stack local.
                resolution: match carrier {
                    Some(fq) => cranelisp_types::VarRef::Global(fq),
                    None => cranelisp_types::VarRef::Local {
                        binder: Symbol::from(callee),
                        binding_span: Span::SYNTHETIC,
                    },
                },
                name: Symbol::from(callee),
                span: Span::new(0, 0),
                resolved_call: None,
                ty: cranelisp_types::ConcreteType::Int,
            }),
            args: vec![],
            span: Span::new(0, 0),
            resolved_call: None,
            ty: ret,
            confined: None,
            escapes: None,
            provenance: None,
            unique_static: None,
        }
    }

    // spec: design/backend/lenient-eval.md §2.8.2 — M-static admission =
    // (recursive-SCC ∧ non-tail), and the Task-0 module-precise self-call fix.
    #[test]
    fn mstatic_admission_and_module_blind_fix() {
        use cranelift::codegen::ir::{Function, UserFuncName};
        use cranelift::prelude::*;
        use cranelift_module::Module;
        use cranelisp_types::{ConcreteType, ModuleFullPath, SymbolTable};
        use dashmap::DashMap;

        use crate::compiler::control_flow::find_sparkable_args_with;

        // Empty call graph: `mstatic_admits_candidate` is fed the `recursive` set
        // directly, so no populated symbol tables are needed. The per-site
        // self-call check (`classify_spark_callee`) recovers direct self-recursion
        // independent of the graph — the seam Task 0 fixes.
        let module_path = ModuleFullPath::from("user");
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        tables.insert(module_path.clone(), SymbolTable::<(), ()>::new(module_path.clone()));

        let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
        let intrinsic_ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).unwrap();
        let func_ids: HashMap<Symbol, cranelift_module::FuncId> = HashMap::new();
        let func_arities: HashMap<Symbol, usize> = HashMap::new();

        let ctx = crate::compiler::CompileContext {
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables: &tables,
            current_module: module_path.clone(),
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc.unwrap(),
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };

        let mut sig = jit.jit_module().make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig);
        let mut fctx = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut func, &mut fctx);
        let mut compiler =
            crate::compiler::FnCompiler::inner(builder, jit.jit_module(), ctx, 1, HashMap::new());

        let empty: HashSet<FQSymbol> = HashSet::new();

        // (1) Direct self-recursion in the current module → admit. The genuine
        //     self-call's callee carries the storage FQ `{user, fib}` (the carve-
        //     out records it); the carrier-keyed `is_self_call` recovers it even
        //     with an empty graph.
        compiler.current_fn_name = Some(Symbol::from("fib"));
        assert!(
            compiler.mstatic_admits_candidate(&apply_var_c("fib", "user", "fib", ConcreteType::Int), &empty),
            "self-recursive non-tail `fib` → admit"
        );

        // (2) Module-precise (FIXME 0654 / S104 Task 0): `other/fib` called from
        //     inside `user/fib` carries the storage FQ `{other, fib}` ≠ the current
        //     identity `{user, fib}`, so `is_self_call` declines it (module AND
        //     symbol must match) — no bare-name false-admit. Empty graph ⇒ declined.
        assert!(
            !compiler.mstatic_admits_candidate(&apply_var_c("other/fib", "other", "fib", ConcreteType::Int), &empty),
            "cross-module same-bare-name `other/fib` is NOT self-recursive → decline"
        );

        // (3) Flat non-recursive accessor → decline (the 0534 firehose class).
        compiler.current_fn_name = Some(Symbol::from("loop"));
        assert!(
            !compiler.mstatic_admits_candidate(&apply_var("cell-at", ConcreteType::Int), &empty),
            "flat non-recursive accessor `cell-at` → decline"
        );

        // (4) Mutual-recursion member (in the recursive-SCC set) → admit.
        let mut rec: HashSet<FQSymbol> = HashSet::new();
        rec.insert(fq("user", "g"));
        assert!(
            compiler.mstatic_admits_candidate(&apply_var("g", ConcreteType::Int), &rec),
            "recursive-SCC member `g` (non-tail) → admit"
        );

        // (5) Through the `find_sparkable_args_with` seam: two recursive
        //     candidates admitted, the flat accessor declined, the ≥2 gate then
        //     returns exactly the two recursive indices.
        compiler.current_fn_name = Some(Symbol::from("fib"));
        let args = vec![
            apply_var_c("fib", "user", "fib", ConcreteType::Int),
            apply_var("cell-at", ConcreteType::Int),
            apply_var_c("fib", "user", "fib", ConcreteType::Int),
        ];
        let idxs =
            find_sparkable_args_with(&args, |e| compiler.mstatic_admits_candidate(e, &empty));
        assert_eq!(
            idxs,
            vec![0, 2],
            "two recursive `fib` candidates admitted, flat `cell-at` declined, ≥2 gate passes"
        );

        // (6) Below the ≥2 gate: a single recursive candidate + flat accessor →
        //     no sparks (the gate suppresses lone candidates).
        let args_one = vec![
            apply_var_c("fib", "user", "fib", ConcreteType::Int),
            apply_var("cell-at", ConcreteType::Int),
        ];
        assert!(
            find_sparkable_args_with(&args_one, |e| compiler.mstatic_admits_candidate(e, &empty))
                .is_empty(),
            "single recursive candidate below the ≥2 gate → no sparks"
        );
    }
}
