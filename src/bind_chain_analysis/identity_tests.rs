//! C7 node identity and C8 callee identity
//! (`design/int/bind-chain-analysis.md` §3.1, §3.6, §6, §7).
//!
//! Every fixture node carries its own span, so a rewrite that reuses one
//! written span on two output nodes is observable.

use std::cell::Cell;
use std::collections::HashMap;

use super::*;
use cranelisp_types::SymbolTable;

type SymbolTables = dashmap::DashMap<ModuleFullPath, SymbolTable>;
use cranelisp_types::{
    DefnVariant, FQSymbol, ModuleAliasEntry, ModuleAliases, Pattern, Program, Scheme, TopLevel,
    Type, Visibility,
};

// ---------------------------------------------------------------------------
// Fixture
// ---------------------------------------------------------------------------

/// Builds expression nodes, each with a fresh span.
struct Nodes {
    next: Cell<u32>,
}

impl Nodes {
    fn new() -> Self {
        Nodes { next: Cell::new(1) }
    }

    fn span(&self) -> Span {
        let n = self.next.get();
        self.next.set(n + 1);
        Span::new(n * 10, n * 10 + 1)
    }

    fn var(&self, name: &str) -> Expr {
        Expr::Var {
            name: Symbol::from(name),
            span: self.span(),
            resolved_call: None,
            inferred_type: None,
        }
    }

    fn int(&self, value: i64) -> Expr {
        Expr::IntLit {
            value,
            span: self.span(),
            inferred_type: None,
        }
    }

    fn call(&self, callee: &str, args: Vec<Expr>) -> Expr {
        Expr::Apply {
            callee: Box::new(self.var(callee)),
            args,
            span: self.span(),
            resolved_call: None,
            inferred_type: None,
        }
    }

    fn lambda(&self, param: &str, body: Expr) -> Expr {
        Expr::Lambda {
            params: vec![(Symbol::from(param), None)],
            body: Box::new(body),
            span: self.span(),
            inferred_type: None,
        }
    }

    /// `(<callee> effect (fn [param] body))`.
    fn step(&self, callee: &str, effect: Expr, param: &str, body: Expr) -> Expr {
        let lambda = self.lambda(param, body);
        self.call(callee, vec![effect, lambda])
    }

    fn bind(&self, effect: Expr, param: &str, body: Expr) -> Expr {
        self.step("bind", effect, param, body)
    }

    fn let_(&self, name: &str, value: Expr, body: Expr) -> Expr {
        Expr::Let {
            bindings: vec![(Symbol::from(name), value)],
            body: Box::new(body),
            span: self.span(),
            inferred_type: None,
        }
    }

    /// Two independent commutative steps: grouped when `callee` is the
    /// primitive.
    fn independent_pair(&self, callee: &str) -> Expr {
        let inner = self.step(callee, self.call("http-get", vec![]), "b", self.int(0));
        self.step(callee, self.call("get-time", vec![]), "a", inner)
    }
}

fn defn(name: &str, params: &[&str], body: Expr) -> TopLevel {
    TopLevel::Defn(Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: params.iter().map(|p| (Symbol::from(*p), None)).collect(),
            body,
            span: Span::new(1, 2),
        }],
        visibility: Visibility::Public,
        span: Span::new(1, 2),
    })
}

fn body_of(program: &Program, name: &str) -> Expr {
    program
        .iter()
        .find_map(|item| match item {
            TopLevel::Defn(d) if d.name.as_ref() == name => Some(d.variants[0].body.clone()),
            _ => None,
        })
        .expect("fixture defines the function")
}

fn int_scheme() -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Int,
    }
}

/// How the module under test sees the `bind` primitive.
enum BindExposure {
    /// No bare exposure: only a qualified spelling reaches it.
    None,
    /// `(import [primitives [bind]])`.
    Import,
    /// The prelude re-exports it and the module falls back to the prelude.
    Prelude,
}

struct Fixture {
    tables: SymbolTables,
    aliases: ModuleAliases,
    prelude: Option<ModuleFullPath>,
    module: ModuleFullPath,
}

const PLATFORM: &str = "platform.test";

impl Fixture {
    /// `primitives` holds the bootstrap `bind` and `sleep`; `platform.test`
    /// holds commutative `get-time`/`http-get` and resource-serial `rd`/`wr`,
    /// all imported bare into `user`.
    fn new(bind: BindExposure) -> Self {
        let tables: SymbolTables = dashmap::DashMap::new();
        let module = ModuleFullPath::from("user");
        let primitives = ModuleFullPath::from("primitives");
        let platform = ModuleFullPath::from(PLATFORM);
        let prelude_path = ModuleFullPath::from("prelude");

        let mut prims = SymbolTable::new(primitives.clone());
        for name in ["bind", "sleep"] {
            prims
                .install_host_promised(
                    Symbol::from(name),
                    int_scheme(),
                    Vec::new(),
                    None,
                    0,
                    Visibility::Public,
                )
                .expect("primitive fixture installs");
        }
        tables.insert(primitives.clone(), prims);

        let mut plat = SymbolTable::new(platform.clone());
        install_platform_effect(
            &mut plat,
            "get-time",
            SchedulingClass::Commutative,
            false,
            0,
        );
        install_platform_effect(
            &mut plat,
            "http-get",
            SchedulingClass::Commutative,
            false,
            1,
        );
        install_platform_effect(&mut plat, "rd", SchedulingClass::ResourceSerial, true, 2);
        install_platform_effect(&mut plat, "wr", SchedulingClass::ResourceSerial, true, 3);
        tables.insert(platform.clone(), plat);

        let mut user = SymbolTable::new(module.clone());
        for name in ["get-time", "http-get", "rd", "wr"] {
            expose(&mut user, name, &platform, name, Visibility::Private);
        }
        expose(
            &mut user,
            "sleep",
            &primitives,
            "sleep",
            Visibility::Private,
        );
        let mut prelude = None;
        match bind {
            BindExposure::None => {}
            BindExposure::Import => {
                expose(&mut user, "bind", &primitives, "bind", Visibility::Private);
            }
            BindExposure::Prelude => {
                let mut table = SymbolTable::new(prelude_path.clone());
                expose(&mut table, "bind", &primitives, "bind", Visibility::Public);
                tables.insert(prelude_path.clone(), table);
                prelude = Some(prelude_path);
            }
        }
        tables.insert(module.clone(), user);

        Fixture {
            tables,
            aliases: ModuleAliases::default(),
            prelude,
            module,
        }
    }

    fn with_user(self, edit: impl FnOnce(&mut SymbolTable)) -> Self {
        edit(&mut self.tables.get_mut(&self.module).expect("user table"));
        self
    }

    /// Runs the pass over `program` through the cluster seam.
    fn run(&self, program: &mut Program) {
        let table = self.tables.get(&self.module).expect("user table");
        let view = cranelisp_types::View::single(&table);
        let scope = cranelisp_types::ResolutionScope::new(
            &self.tables,
            &self.aliases,
            &view,
            &self.module,
            self.prelude.as_ref(),
        );
        crate::session_setup::apply_bind_chain_analysis(program, &scope, &self.module);
    }
}

fn expose(
    table: &mut SymbolTable,
    spelling: &str,
    home: &ModuleFullPath,
    name: &str,
    visibility: Visibility,
) {
    table
        .expose_candidate(
            Symbol::from(spelling),
            FQSymbol {
                module: home.clone(),
                symbol: Symbol::from(name),
            },
            visibility,
        )
        .expect("import fixture installs");
}

fn install_platform_effect(
    table: &mut SymbolTable,
    name: &str,
    class: SchedulingClass,
    poll_shape: bool,
    slot: usize,
) {
    table
        .install_platform(
            Symbol::from(name),
            int_scheme(),
            Vec::new(),
            None,
            0,
            class,
            poll_shape,
            slot,
            Visibility::Public,
        )
        .expect("platform-effect fixture installs");
}

/// Runs the pass and returns `main`'s body before and after.
fn schedule(fx: &Fixture, mut program: Program) -> (Expr, Expr) {
    let before = body_of(&program, "main");
    fx.run(&mut program);
    (before, body_of(&program, "main"))
}

fn unchanged(before: &Expr, after: &Expr) -> bool {
    format!("{before:?}") == format!("{after:?}")
}

// ---------------------------------------------------------------------------
// C7 — node identity
// ---------------------------------------------------------------------------

/// Every expression span in `expr`, in walk order.
fn spans(expr: &Expr, out: &mut Vec<Span>) {
    out.push(expr_span(expr));
    match expr {
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            bindings.iter().for_each(|(_, v)| spans(v, out));
            spans(body, out);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            spans(cond, out);
            spans(then_branch, out);
            spans(else_branch, out);
        }
        Expr::Lambda { body, .. } | Expr::Trace { body, .. } => spans(body, out),
        Expr::Annotate { expr, .. } => spans(expr, out),
        Expr::Apply { callee, args, .. } => {
            spans(callee, out);
            args.iter().for_each(|a| spans(a, out));
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            spans(scrutinee, out);
            arms.iter().for_each(|arm| spans(&arm.body, out));
        }
        Expr::VecLit { elements, .. } => elements.iter().for_each(|e| spans(e, out)),
        Expr::ConstrADT { fields, .. } => fields.iter().for_each(|f| spans(f, out)),
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            spans(launched, out);
            spans(continuation, out);
        }
    }
}

fn expr_span(expr: &Expr) -> Span {
    match expr {
        Expr::IntLit { span, .. }
        | Expr::FloatLit { span, .. }
        | Expr::BoolLit { span, .. }
        | Expr::StringLit { span, .. }
        | Expr::Var { span, .. }
        | Expr::Let { span, .. }
        | Expr::If { span, .. }
        | Expr::Lambda { span, .. }
        | Expr::Apply { span, .. }
        | Expr::Match { span, .. }
        | Expr::VecLit { span, .. }
        | Expr::Annotate { span, .. }
        | Expr::ParBind { span, .. }
        | Expr::Trace { span, .. }
        | Expr::LaunchContinue { span, .. }
        | Expr::ConstrADT { span, .. } => *span,
    }
}

/// The written spans of each one-parameter step `(callee effect (fn [p] …))`,
/// keyed by its parameter: (application, callee, lambda).
fn step_spans(expr: &Expr, out: &mut HashMap<Symbol, (Span, Span, Span)>) {
    if let Expr::Apply {
        callee, args, span, ..
    } = expr
        && args.len() == 2
        && let Expr::Lambda {
            params,
            span: lambda_span,
            ..
        } = &args[1]
        && params.len() == 1
    {
        out.insert(
            params[0].0.clone(),
            (*span, expr_span(callee), *lambda_span),
        );
    }
    let mut children = Vec::new();
    direct_children(expr, &mut children);
    children.into_iter().for_each(|c| step_spans(c, out));
}

fn direct_children<'e>(expr: &'e Expr, out: &mut Vec<&'e Expr>) {
    match expr {
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            out.extend(bindings.iter().map(|(_, v)| v));
            out.push(body);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => out.extend([cond.as_ref(), then_branch, else_branch]),
        Expr::Lambda { body, .. } | Expr::Trace { body, .. } => out.push(body),
        Expr::Annotate { expr, .. } => out.push(expr),
        Expr::Apply { callee, args, .. } => {
            out.push(callee);
            out.extend(args.iter());
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            out.push(scrutinee);
            out.extend(arms.iter().map(|arm| &arm.body));
        }
        Expr::VecLit { elements, .. } => out.extend(elements.iter()),
        Expr::ConstrADT { fields, .. } => out.extend(fields.iter()),
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => out.extend([launched.as_ref(), continuation]),
    }
}

/// C7: the pass mints no span, no output span sits on two nodes, and every
/// sequential step keeps its written application, callee and lambda spans.
fn assert_node_identity(shape: &str, body: Expr) {
    let fx = Fixture::new(BindExposure::Import);
    let (before, after) = schedule(&fx, vec![defn("main", &["t", "u"], body)]);

    let mut written = Vec::new();
    spans(&before, &mut written);
    let mut emitted = Vec::new();
    spans(&after, &mut emitted);
    let mut seen = std::collections::HashSet::new();
    for span in &emitted {
        assert!(written.contains(span), "{shape}: the pass minted {span:?}");
        assert!(
            seen.insert(*span),
            "{shape}: {span:?} is on two output nodes: {after:?}"
        );
    }

    let mut written_steps = HashMap::new();
    step_spans(&before, &mut written_steps);
    let mut emitted_steps = HashMap::new();
    step_spans(&after, &mut emitted_steps);
    for (param, spans) in &emitted_steps {
        if let Some(expected) = written_steps.get(param) {
            assert_eq!(
                spans, expected,
                "{shape}: step `{param}` must keep its written (application, callee, lambda) spans"
            );
        }
    }
}

// spec: design/int/bind-chain-analysis.md §3.6 — C7, one sequential step
#[test]
fn rebuilt_single_step_keeps_written_node_spans() {
    let n = Nodes::new();
    let body = n.bind(n.call("get-time", vec![]), "a", n.var("a"));
    assert_node_identity("one step", body);
}

// spec: design/int/bind-chain-analysis.md §3.6 — C7, a two-step chain
#[test]
fn rebuilt_two_step_chain_keeps_written_node_spans() {
    let n = Nodes::new();
    let inner = n.bind(n.call("http-get", vec![n.var("a")]), "b", n.var("b"));
    let body = n.bind(n.call("get-time", vec![]), "a", inner);
    assert_node_identity("two-step chain", body);
}

// spec: design/int/bind-chain-analysis.md §3.6 — C7, a parallel group then a
// sequential step
#[test]
fn parallel_group_then_sequential_step_keeps_written_node_spans() {
    let n = Nodes::new();
    let third = n.bind(
        n.call("http-get", vec![n.var("b")]),
        "c",
        n.call("add", vec![n.var("a"), n.var("c")]),
    );
    let second = n.bind(n.call("http-get", vec![]), "b", third);
    let body = n.bind(n.call("get-time", vec![]), "a", second);
    assert_node_identity("parallel group then sequential", body);
}

// spec: design/int/bind-chain-analysis.md §3.6 — C7, a launched step
#[test]
fn launched_step_keeps_written_node_spans() {
    let n = Nodes::new();
    let after = n.bind(n.call("get-time", vec![]), "k", n.var("k"));
    let body = n.bind(n.call("rd", vec![n.var("t")]), "r", after);
    assert_node_identity("launched step", body);
}

// spec: design/int/bind-chain-analysis.md §3.6 — C7, a chain inside an effect
// expression
#[test]
fn chain_inside_effect_expression_keeps_written_node_spans() {
    let n = Nodes::new();
    let inner = n.bind(n.call("get-time", vec![]), "x", n.var("x"));
    let body = n.bind(inner, "y", n.var("y"));
    assert_node_identity("chain inside an effect expression", body);
}

// spec: design/int/bind-chain-analysis.md §3.6 — C7, chains under a lambda, a
// match arm and a let
#[test]
fn chains_under_lambda_match_and_let_keep_written_node_spans() {
    let n = Nodes::new();
    let under_lambda = n.lambda("z", n.bind(n.call("get-time", vec![]), "p", n.var("p")));
    let under_arm = Expr::Match {
        scrutinee: Box::new(n.var("t")),
        arms: vec![MatchArm {
            pattern: Pattern::Var {
                name: Symbol::from("w"),
                span: n.span(),
            },
            body: n.bind(n.call("get-time", vec![]), "q", n.var("q")),
            span: n.span(),
        }],
        span: n.span(),
        compiler_generated: false,
        inferred_type: None,
    };
    let under_let = n.let_(
        "l",
        n.int(1),
        n.bind(n.call("get-time", vec![]), "s", n.var("s")),
    );
    let body = n.call("tuple", vec![under_lambda, under_arm, under_let]);
    assert_node_identity("chains under lambda, match arm and let", body);
}

// ---------------------------------------------------------------------------
// C8 — callee identity: subjects that must decline
// ---------------------------------------------------------------------------

/// A user `bind` declared in the cluster, beside the prelude's primitive.
// spec: spec/04-expressions.md §4.6 — C8, a cluster declaration declines
#[test]
fn user_bind_declared_in_the_cluster_is_not_the_primitive() {
    let fx = Fixture::new(BindExposure::Prelude);
    let n = Nodes::new();
    let user_bind = defn("bind", &["io", "f"], n.var("io"));
    let (before, after) = schedule(
        &fx,
        vec![user_bind, defn("main", &[], n.independent_pair("bind"))],
    );
    assert!(
        unchanged(&before, &after),
        "a cluster's own `bind` must be left as written: {after:?}"
    );
}

// spec: spec/04-expressions.md §4.6 — C8, a committed user `bind` declines
#[test]
fn user_bind_committed_by_an_earlier_turn_is_not_the_primitive() {
    let fx = Fixture::new(BindExposure::None).with_user(|user| {
        user.install_host_promised(
            Symbol::from("bind"),
            int_scheme(),
            Vec::new(),
            None,
            0,
            Visibility::Public,
        )
        .expect("user bind installs");
    });
    let n = Nodes::new();
    let (before, after) = schedule(&fx, vec![defn("main", &[], n.independent_pair("bind"))]);
    assert!(
        unchanged(&before, &after),
        "a committed user `bind` must be left as written: {after:?}"
    );
}

// spec: spec/04-expressions.md §4.6 — C8, a parameter named `bind` declines
#[test]
fn parameter_named_bind_is_not_the_primitive() {
    let fx = Fixture::new(BindExposure::Import);
    let n = Nodes::new();
    let (before, after) = schedule(
        &fx,
        vec![defn("main", &["bind"], n.independent_pair("bind"))],
    );
    assert!(
        unchanged(&before, &after),
        "a parameter `bind` must be left as written: {after:?}"
    );
}

// spec: spec/04-expressions.md §4.6 — C8, a `let` named `bind` declines
#[test]
fn let_named_bind_is_not_the_primitive() {
    let fx = Fixture::new(BindExposure::Import);
    let n = Nodes::new();
    let body = n.let_("bind", n.var("k"), n.independent_pair("bind"));
    let (before, after) = schedule(&fx, vec![defn("main", &["k"], body)]);
    assert!(
        unchanged(&before, &after),
        "a `let`-bound `bind` must be left as written: {after:?}"
    );
}

// spec: spec/04-expressions.md §4.6 — C8, a self-qualified user `bind` declines
#[test]
fn self_qualified_user_bind_is_not_the_primitive() {
    let fx = Fixture::new(BindExposure::Import);
    let n = Nodes::new();
    let user_bind = defn("bind", &["io", "f"], n.var("io"));
    let (before, after) = schedule(
        &fx,
        vec![
            user_bind,
            defn("main", &[], n.independent_pair("user/bind")),
        ],
    );
    assert!(
        unchanged(&before, &after),
        "`user/bind` names the user's function: {after:?}"
    );
}

// spec: spec/08-modules.md §8.6.5 — C8, an ambiguous spelling declines
#[test]
fn ambiguous_bind_is_not_the_primitive() {
    let other = ModuleFullPath::from("other");
    let fx = Fixture::new(BindExposure::Import).with_user(|user| {
        expose(user, "bind", &other, "bind", Visibility::Private);
    });
    let mut other_table = SymbolTable::new(other.clone());
    other_table
        .install_host_promised(
            Symbol::from("bind"),
            int_scheme(),
            Vec::new(),
            None,
            0,
            Visibility::Public,
        )
        .expect("other bind installs");
    fx.tables.insert(other, other_table);
    let n = Nodes::new();
    let (before, after) = schedule(&fx, vec![defn("main", &[], n.independent_pair("bind"))]);
    assert!(
        unchanged(&before, &after),
        "an ambiguous `bind` must be left as written: {after:?}"
    );
}

// spec: spec/04-expressions.md §4.6 — C8, a parameter spelled like a platform
// function is not that effect (REPRO-1065-e)
#[test]
fn parameter_named_like_a_platform_effect_is_not_scheduled() {
    let fx = Fixture::new(BindExposure::Import);
    let n = Nodes::new();
    let inner = n.bind(n.call("get-time", vec![]), "b", n.int(0));
    let body = n.bind(n.call("get-time", vec![]), "a", inner);
    let (before, after) = schedule(&fx, vec![defn("main", &["get-time"], body)]);
    assert!(
        unchanged(&before, &after),
        "a local `get-time` is not the platform effect: {after:?}"
    );
}

// spec: spec/10-io.md §10.12.7 — C8, a local spelled `sleep` is not the timer
// leaf, so the handler that calls it is not launched
#[test]
fn local_named_sleep_is_not_the_timer_leaf() {
    let n = Nodes::new();
    let handler = |n: &Nodes| {
        n.bind(
            n.call("rd", vec![n.var("t")]),
            "req",
            n.bind(
                n.call("sleep", vec![n.int(5)]),
                "z",
                n.call("wr", vec![n.var("t"), n.var("req")]),
            ),
        )
    };
    let launched = |params: &[&str], n: &Nodes| {
        let fx = Fixture::new(BindExposure::Import);
        let body = n.bind(handler(n), "_", n.call("recur", vec![n.var("l")]));
        let (_, after) = schedule(&fx, vec![defn("main", params, body)]);
        matches!(after, Expr::LaunchContinue { .. })
    };
    assert!(
        launched(&["t", "l"], &n),
        "control: the timer leaf launches inside the handler"
    );
    assert!(
        !launched(&["t", "l", "sleep"], &n),
        "a local `sleep` is an opaque effect position"
    );
}

// ---------------------------------------------------------------------------
// C8 — callee identity: subjects that must be recognised
// ---------------------------------------------------------------------------

fn groups(fx: &Fixture, callee: &str) -> bool {
    let n = Nodes::new();
    let (_, after) = schedule(fx, vec![defn("main", &[], n.independent_pair(callee))]);
    matches!(after, Expr::ParBind { .. })
}

// spec: spec/10-io.md §10.12.1 — C8, the primitive through an import
#[test]
fn imported_primitive_bind_is_recognised() {
    assert!(groups(&Fixture::new(BindExposure::Import), "bind"));
}

// spec: spec/10-io.md §10.12.1 — C8, the primitive through the prelude fallback
#[test]
fn prelude_primitive_bind_is_recognised() {
    assert!(groups(&Fixture::new(BindExposure::Prelude), "bind"));
}

// spec: spec/10-io.md §10.12.1 — C8, the qualified `primitives/bind`
#[test]
fn qualified_primitive_bind_is_recognised() {
    assert!(groups(&Fixture::new(BindExposure::None), "primitives/bind"));
}

// spec: spec/10-io.md §10.12.1 — C8, the primitive through a module alias
#[test]
fn aliased_primitive_bind_is_recognised() {
    let fx = Fixture::new(BindExposure::None);
    fx.aliases.insert(
        cranelisp_types::module_alias_key(&fx.module, "p"),
        ModuleAliasEntry::new(
            ModuleFullPath::from("primitives"),
            Visibility::Private,
            Span::SYNTHETIC,
        ),
    );
    assert!(groups(&fx, "p/bind"));
}
