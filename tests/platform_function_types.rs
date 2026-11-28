mod helpers;
use helpers::e2e::Cranelisp;

fn signature(platform: &str, mode: &str) -> helpers::e2e::CrOutput {
    let cr = Cranelisp::new().use_workspace_platforms()
        .file("holder.cl", "(deftype Callback [:(Fn [primitives/Int] primitives/Int) f])")
        .user(&format!("(import [holder [Callback]])\n(platform {platform})\n(defn main [] (primitives/pure 0))"));
    if mode == "run" {
        cr.run("user.cl").output()
    } else {
        cr.stdin("7\n").output()
    }
}

// spec: spec/10-io.md §10.10.1
// defect: class=silent-accept locus=src/platform.rs::register_platform_in_tc found=S125 owner=/dev
#[test]
fn s125_0979_fnparam_neg_run() {
    let out = signature("fnparam", "run");
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("bad-param")
            && (diag.contains("function type")
                || diag.contains("function-typed")
                || diag.contains("Fn"))
            && diag.contains("error"),
        "platform load must refuse bad-param for function containment: {diag}"
    );
}

// spec: spec/10-io.md §10.10.1
// defect: class=silent-accept locus=src/platform.rs::register_platform_in_tc found=S125 owner=/dev
#[test]
fn s125_0979_fnparam_neg_repl() {
    let out = signature("fnparam", "repl");
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("bad-param")
            && (diag.contains("function type")
                || diag.contains("function-typed")
                || diag.contains("Fn"))
            && diag.contains("error"),
        "platform load must refuse bad-param for function containment: {diag}"
    );
}

// spec: spec/10-io.md §10.10.1
// defect: class=silent-accept locus=src/platform.rs::register_platform_in_tc found=S125 owner=/dev
#[test]
fn s125_0979_fnresult_neg_run() {
    let out = signature("fnresult", "run");
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("bad-result")
            && (diag.contains("function type")
                || diag.contains("function-typed")
                || diag.contains("Fn"))
            && diag.contains("error"),
        "platform load must refuse bad-result for function containment: {diag}"
    );
}

// spec: spec/10-io.md §10.10.1
// defect: class=silent-accept locus=src/platform.rs::register_platform_in_tc found=S125 owner=/dev
#[test]
fn s125_0979_fnresult_neg_repl() {
    let out = signature("fnresult", "repl");
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("bad-result")
            && (diag.contains("function type")
                || diag.contains("function-typed")
                || diag.contains("Fn"))
            && diag.contains("error"),
        "platform load must refuse bad-result for function containment: {diag}"
    );
}

// spec: spec/10-io.md §10.10.1
// defect: class=silent-accept locus=src/platform.rs::register_platform_in_tc found=S125 owner=/dev
#[test]
fn s125_0979_fnfield_neg_run() {
    let out = signature("fnfield", "run");
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("bad-field")
            && (diag.contains("function type")
                || diag.contains("function-typed")
                || diag.contains("Fn"))
            && diag.contains("error"),
        "platform load must refuse bad-field for function containment: {diag}"
    );
}

// spec: spec/10-io.md §10.10.1
// defect: class=silent-accept locus=src/platform.rs::register_platform_in_tc found=S125 owner=/dev
#[test]
fn s125_0979_fnfield_neg_repl() {
    let out = signature("fnfield", "repl");
    let diag = format!("{}{}", out.stdout, out.stderr);
    assert!(
        diag.contains("bad-field")
            && (diag.contains("function type")
                || diag.contains("function-typed")
                || diag.contains("Fn"))
            && diag.contains("error"),
        "platform load must refuse bad-field for function containment: {diag}"
    );
}

// spec: spec/10-io.md §10.10.1
#[test]
fn s125_0979_ordinary_control_run() {
    let cr = Cranelisp::new()
        .use_workspace_platforms()
        .user("(platform fngood) (import [platform.fngood [ordinary]]) (defn main [] (ordinary))");
    cr.run("user.cl").output().assert_exit(42);
}

// spec: spec/10-io.md §10.10.1
#[test]
fn s125_0979_ordinary_control_repl() {
    let cr = Cranelisp::new()
        .use_workspace_platforms()
        .user("(platform fngood) (import [platform.fngood [ordinary]]) (defn main [] (ordinary))");
    cr.stdin("(main)\n")
        .output()
        .assert_ok()
        .assert_stdout_contains(":primitives/Int 42");
}
