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
        let MonoExpr::Apply { callee, span, .. } = candidate else {
            return None;
        };
        let MonoExpr::Var { name, .. } = callee.as_ref() else {
            return None;
        };
        let fq = callee_fqsymbol(&self.ctx.current_module, name);
        let is_self = self
            .current_fn_name
            .as_ref()
            .is_some_and(|cur| bare_name(cur.as_ref()) == bare_name(name.as_ref()));
        let scc = is_self || recursive.contains(&fq);
        Some((fq.to_string(), scc, false, *span))
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
}
