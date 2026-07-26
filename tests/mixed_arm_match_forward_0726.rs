// mixed_arm_match_forward_0726.rs — the tripwire for FIXME 0726
// (`design/arch/fixmes/0726-qa-mixed-arm-match-forward-tripwire.md`, filed by
// `/design`(backend) in S115 Phase 3 to discharge 0697's second ask). Authored
// by `/testing` in S118 W1 per `tests/plan/s118-test-plan.md` §4.2 / §2.3 as
// INTENDED REDs that would flip with the Track-B W3 per-arm release migration
// (`design/backend/transitive-drop-glue.md` §5 removes exactly the approximation
// this file fences).
//
// FIXED — S118 W3 slice S3, `22072a0c`. Both tripwire cells are GREEN and are
// now regression guards; read what follows in the PAST tense. The `// defect:`
// locus still names `fn_compiler.rs::match_forwards_scrutinee`, which is where
// the defect lived. That function SURVIVES the fix — but only as
// `operand_live_binding_root`'s provenance trace, which is genuinely an
// any-arm question. Its RELEASE-GATE use, and the merge-block dec it gated, are
// gone: `match_codegen.rs::scrutinee_lifetime_for_arm` now resolves a per-ARM
// lifetime, so the ctor path releases what it consumed regardless of what a
// sibling var arm does. A regression here would most likely be a new whole-match
// approximation, not this one returning.
//
// THE APPROXIMATION UNDER TEST. The R3 forwarding-suppresses-dec accounting uses
// a STATIC WHOLE-MATCH predicate — `fn_compiler.rs::match_forwards_scrutinee`
// answers "does ANY var-pattern arm forward its binder?" — and emits the
// scrutinee-dec suppression ONCE, in the merge block. For a MIXED
// constructor + var-default match, the suppression is therefore applied on ALL
// paths, including the paths where the ctor arm ran and nothing forwarded
// anything. A run that selects the CTOR arm never decs the consumed temporary
// scrutinee.
//
// WHY IT WAS PARKED, AND WHY IT NEEDS A FENCE ANYWAY. The residue is leak-only
// and O(depth) — never a UAF — so `binding-indirection-consume.md` §2 recorded
// it, argued the polarity, NAMED the mechanism-complete alternative (per-arm dec
// placement) and parked it. What the park had no answer for is that the parked
// boundary had NO TEST: the leak is invisible to the both-polarity differential
// oracle (it is identical with ownership analysis ON and OFF, so the two
// lowerings share it — the FIXME-0761 blindness), and it is invisible to any
// residue allowance that tolerates a small constant. A parked approximation with
// no fence is indistinguishable from an unnoticed defect the day its residue
// stops being small.
//
// THE CELLS (plan §4.2): mixed ctor+var match × {ctor-path selected, var-path
// selected} × {toggle ON, toggle OFF}, asserting ABSOLUTE `allocs == deallocs`
// — never a differential and never an allowance — plus one `--link` face.
//
// MEASURED AT HEAD `e15ff20f` (`--run`, PrimitivesOnly, `--no-cache`,
// `CRANELISP_NO_LENIENT=1`):
//
//   selected path   toggle   exit   allocs/deallocs   residue
//   ctor arm        ON        3        4 / 2            2      ← RED
//   ctor arm        OFF       3        4 / 2            2      ← RED
//   var  arm        ON        3        3 / 3            0      ← GREEN control
//   var  arm        OFF       3        3 / 3            0      ← GREEN control
//
// The value is RIGHT on every row — this defect never produces a wrong answer,
// which is precisely why only an exact-balance assertion can see it. The
// toggle-independence is the FIXME-0761 signature reproduced: a fence built on
// the differential face would report GREEN on all four rows.
//
// THE PAIR IS THE POINT. ctor-path RED against var-path GREEN, same program,
// same match, same types, one boolean of difference — the only variable is which
// arm ran. That is what identifies the whole-match approximation as the
// mechanism rather than "matches over owned temporaries leak", and it is the
// pair a per-arm release plan has to turn into GREEN/GREEN.
//
// WHAT A FIX MUST NOT DO. Making the ctor path balance by suppressing the
// var-path forward would turn the var-path cell into an OVER-release (the
// forwarded scrutinee freed while the caller still holds it), so the var-path
// cells assert balance too rather than being left as commentary. Both polarities
// are on the fence, in both toggles.
//
// Free-standing: `PreludeVariant::PrimitivesOnly`, zero stdlib.
// `CRANELISP_NO_LENIENT=1` on every run — no sparks in these shapes, and it
// keeps the RC counts deterministic (tests/CLAUDE.md §"RC tests run serially").

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// ===========================================================================
// The program
// ===========================================================================

/// The mixed-arm shape from FIXME 0726, reduced: `pick` matches an owned
/// temporary with ONE constructor arm and a var-default arm that FORWARDS its
/// binder (`x x`), which is what arms the whole-match suppression for every
/// path.
///
///  - `selector = true`  → `norm` yields `(Jus …)`, the CTOR arm runs. Its body
///    takes the payload over into a fresh `Non`, so the consumed `Jus` box is
///    the matching frame's to release — and is not released. **The RED path.**
///  - `selector = false` → `norm` yields `(Non …)`, no constructor arm matches,
///    the var-default arm runs and forwards the whole scrutinee out. The
///    suppression is CORRECT here. **The GREEN control path.**
///
/// Both constructors carry a heap field, so the two paths differ only in which
/// arm ran — not in what was allocated. The answer is 3 either way.
fn mixed_arm_program(selector: bool) -> String {
    format!(
        "(deftype O (Non [a]) (Jus [b]))\n\
         (defn norm [f] (if f (Jus [1 2 3]) (Non [4 5 6])))\n\
         (defn pick [f] (match (norm f) [(Jus g) (Non g) x x]))\n\
         (defn main [] (Pure (match (pick {selector}) \
         [(Jus g) (vec-len g) (Non g) (vec-len g)])))\n"
    )
}

// ===========================================================================
// Measurement
// ===========================================================================

struct Measure {
    exit: Option<i32>,
    rc: Option<(i64, i64)>,
    stderr: String,
}

fn measure(program: &str, ownership_off: bool, link: bool) -> Measure {
    let mut b = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .user(program)
        .env("CRANELISP_RC_STATS", "1")
        .env("CRANELISP_NO_LENIENT", "1");
    b = if link {
        b.link_then_run("user.cl")
    } else {
        b.run("user.cl")
    };
    if ownership_off {
        b = b.env("CRANELISP_NO_OWNERSHIP", "1");
    }
    let out = b.output();
    // The LAST `[RC_STATS]` line: under `--link` the compiler process and the
    // produced binary each emit one, and the produced binary's is last.
    let rc = out
        .stderr
        .lines()
        .rev()
        .find(|l| l.contains("[RC_STATS]"))
        .and_then(|line| {
            let field = |k: &str| -> Option<i64> {
                line.split_whitespace()
                    .find_map(|t| t.strip_prefix(k).and_then(|v| v.parse().ok()))
            };
            Some((field("allocs=")?, field("deallocs=")?))
        });
    Measure {
        exit: out.status.code(),
        rc,
        stderr: out.stderr.clone(),
    }
}

/// The whole contract for one cell in one mode and one toggle state: the program
/// computes 3, terminates normally, and `allocs == deallocs` EXACTLY — no
/// residue allowance in either direction (an over-release is the polarity a
/// tolerance is blind to in principle).
fn assert_contract(label: &str, program: &str, ownership_off: bool, link: bool) {
    let m = measure(program, ownership_off, link);
    let toggle = if ownership_off {
        "CRANELISP_NO_OWNERSHIP=1"
    } else {
        "ownership ON"
    };
    let mode = if link { "--link" } else { "--run" };
    assert_eq!(
        m.exit,
        Some(3),
        "[{label}] {mode} ({toggle}) MUST compute 3 and terminate normally; got \
         exit {:?}.\nstderr:\n{}",
        m.exit,
        m.stderr
    );
    let (allocs, deallocs) = m.rc.unwrap_or_else(|| {
        panic!(
            "[{label}] {mode} ({toggle}) emitted no [RC_STATS] line:\n{}",
            m.stderr
        )
    });
    assert_eq!(
        allocs,
        deallocs,
        "[{label}] {mode} ({toggle}) MUST balance EXACTLY: allocs={allocs} \
         deallocs={deallocs} (residue {}). The scrutinee-dec suppression is a \
         WHOLE-MATCH decision taken in the merge block, so a run that selected \
         the constructor arm — where nothing forwards anything — inherits the \
         var-arm's suppression and never releases the consumed temporary. The \
         release decision belongs per ARM.",
        allocs - deallocs
    );
}

/// Both `--run` toggle legs. The faces are measured toggle-independent (the
/// FIXME-0761 blindness), so a divergence here is itself new information.
fn assert_both_toggles(label: &str, program: &str) {
    assert_contract(label, program, false, false);
    assert_contract(label, program, true, false);
}

// ===========================================================================
// THE TRIPWIRE — ctor path selected (FIXED S118/22072a0c)
// ===========================================================================

// The formerly-RED half of the pair. `(match (norm true) [(Jus g) (Non g) x x])`
// selects the CONSTRUCTOR arm; the arm takes the payload over into a fresh `Non`,
// so the consumed `Jus` box is unreachable the moment the arm body has it — and
// the whole-match suppression, armed by the sibling var arm, meant nobody decced
// it. Residue 2 at the S118 W1 HEAD, identical in both toggles.
// spec: spec/12-runtime.md §12.3.1 — a heap value MUST be freed when it is no
// longer reachable. The consumed scrutinee of a constructor arm is unreachable
// once the arm has taken over its payload.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::match_forwards_scrutinee — whole-match forwarding predicate suppresses the scrutinee dec on ALL paths of a mixed ctor+var match found=S115 fixed=S118/22072a0c owner=/dev
#[test]
fn mixed_arm_match_ctor_path_releases_the_consumed_scrutinee() {
    assert_both_toggles("0726 ctor-path", &mixed_arm_program(true));
}

// The `--link` face of the formerly-RED half. Pinned separately because `--link` is the
// release gate and because this family's sibling defects (0782/0810 Face B)
// showed the two modes can disagree in SYMPTOM while sharing a cause — a fix
// that lands only on the JIT path is a `mode-divergence` defect in its own right.
// spec: spec/12-runtime.md §12.3.1 — the requirement is on the language, not on
// a mode; `--run` and `--link` MUST agree.
// defect: class=rc-miscount locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::match_forwards_scrutinee — whole-match forwarding suppression, `--link` face found=S115 fixed=S118/22072a0c owner=/dev
#[test]
fn mixed_arm_match_ctor_path_releases_the_consumed_scrutinee_linked() {
    assert_contract("0726 ctor-path link", &mixed_arm_program(true), false, true);
}

// ===========================================================================
// THE DISCRIMINATING CONTROL — var path selected (GREEN, and must stay GREEN)
// ===========================================================================

// The GREEN half of the pair: the SAME program with the selector flipped, so the
// var-default arm runs and forwards the whole scrutinee out of the match. Here
// the suppression is exactly right and the program balances (3/3, both toggles).
//
// This control is what makes the RED above attributable to the WHOLE-MATCH grain
// of the predicate rather than to "matches over owned temporaries leak", and it
// is the fence against the obvious wrong fix: decing unconditionally in the
// merge block would free the value this path forwards to its caller, turning
// this cell into an over-release. Balance is asserted here in both directions
// for that reason.
// spec: spec/06-pattern-matching.md §6.2.4 — a variable pattern binds the whole
// scrutinee for its arm; forwarding it out of the match transfers the reference
// rather than ending it.
#[test]
fn control_mixed_arm_match_var_path_forwards_without_leak_green() {
    assert_both_toggles("0726 var-path control", &mixed_arm_program(false));
}

// The `--link` face of the GREEN control, so the RED `--link` cell above is read
// against a same-mode GREEN rather than against `--run`.
// spec: spec/06-pattern-matching.md §6.2.4 — same requirement, `--link` mode.
#[test]
fn control_mixed_arm_match_var_path_forwards_without_leak_green_linked() {
    assert_contract(
        "0726 var-path control link",
        &mixed_arm_program(false),
        false,
        true,
    );
}
