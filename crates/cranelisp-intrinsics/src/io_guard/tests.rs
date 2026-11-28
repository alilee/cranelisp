// The trap guard's cells (`design/intrinsics/process-lifecycle.md` §1.8).
// Cells that change a disposition, or let a trap end the process, run in a
// child process (`crate::test_child`); the rest run in their own nextest
// process. Signals are delivered with `libc::raise`, which drives the same
// handler path a hardware trap in foreign code takes without memory UB.
use super::*;
use crate::source_census::{expected, production_sources, token_sites};
use crate::test_child::{self, selected};
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, Barrier};

const TRAP_SIGNALS: [(libc::c_int, &str); 4] = [
    (libc::SIGFPE, "SIGFPE"),
    (libc::SIGILL, "SIGILL"),
    (libc::SIGBUS, "SIGBUS"),
    (libc::SIGSEGV, "SIGSEGV"),
];

fn child(name: &str) -> String {
    test_child::child_path(module_path!(), name)
}

/// The child's reported lines that start with one of `markers`, in order. A
/// report can follow libtest's `test <name> ... ` on the same line, so each is
/// read from its marker.
fn reported<'a>(stdout: &'a str, markers: &[&str]) -> Vec<&'a str> {
    stdout
        .lines()
        .filter_map(|line| {
            markers
                .iter()
                .filter_map(|marker| line.find(marker))
                .min()
                .map(|at| &line[at..])
        })
        .collect()
}

/// The action currently installed for `sig`, read without changing it.
fn installed_action(sig: libc::c_int) -> libc::sigaction {
    // SAFETY: a null new action makes `sigaction` a pure query into `action`.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        assert_eq!(libc::sigaction(sig, std::ptr::null(), &mut action), 0);
        action
    }
}

/// Put `sig` back to the default action, so an unrecovered trap kills the child
/// by that signal.
fn default_action(sig: libc::c_int) {
    // SAFETY: installing `SIG_DFL` is always valid.
    unsafe { libc::signal(sig, libc::SIG_DFL) };
}

fn raise(sig: libc::c_int) {
    // SAFETY: `raise` delivers `sig` synchronously to this thread.
    unsafe { libc::raise(sig) };
}

// spec: spec/12-runtime.md §12.7.6 — a trap inside a guarded extent returns
// the trapping signal to the guard's caller.
#[test]
fn trap_in_a_guarded_extent_returns_its_signal() {
    let outcome = run_trap_guarded(|| {
        raise(libc::SIGSEGV);
        0
    });
    assert_eq!(outcome, Err(TrapSignal(libc::SIGSEGV)));
}

// spec: spec/12-runtime.md §12.7.6 — a guarded extent routes all four trap
// signals to the guard's handler.
#[test]
fn guarded_extent_routes_all_four_trap_signals_to_the_guard() {
    let handlers =
        run_trap_guarded(|| TRAP_SIGNALS.map(|(sig, _)| installed_action(sig))).expect("no trap");
    for ((_, name), action) in TRAP_SIGNALS.iter().zip(handlers) {
        assert_eq!(
            action.sa_sigaction,
            trap_handler_address(),
            "{name} is routed to the guard"
        );
    }
}

// --- Cell 1: overlap -------------------------------------------------------

#[test]
fn child_traps_while_another_thread_returns() {
    if !selected("child_traps_while_another_thread_returns") {
        return;
    }
    default_action(libc::SIGSEGV);
    // A enters; B enters; A returns; B raises.
    let a_inside = Arc::new(Barrier::new(2));
    let b_inside = Arc::new(Barrier::new(2));
    let a_returned = Arc::new(Barrier::new(2));
    let a = {
        let (a_inside, b_inside, a_returned) =
            (a_inside.clone(), b_inside.clone(), a_returned.clone());
        std::thread::spawn(move || {
            run_trap_guarded(|| {
                a_inside.wait();
                b_inside.wait();
            })
            .expect("A does not trap");
            a_returned.wait();
        })
    };
    a_inside.wait();
    let outcome = run_trap_guarded(|| {
        b_inside.wait();
        a_returned.wait();
        raise(libc::SIGSEGV);
    });
    a.join().unwrap();
    println!("B: {:?}", outcome);
}

// spec: spec/12-runtime.md §12.7.6 — thread A's protected call returns while
// thread B is inside one; B then traps, and B's call still reports the signal.
// Barriers fix the order.
#[test]
fn guarded_return_on_one_thread_keeps_another_threads_protection() {
    let end = test_child::run(&child("child_traps_while_another_thread_returns"), &[]);
    assert_eq!((end.code, end.signal), (Some(0), None), "{}", end.stderr);
    let line = format!("B: Err(TrapSignal({}))", libc::SIGSEGV);
    assert_eq!(
        reported(&end.stdout, &["B: "]),
        [line.as_str()],
        "{}",
        end.stdout
    );
}

// --- Cell 2: no restore ----------------------------------------------------

#[test]
fn child_reports_actions_after_a_guarded_return() {
    if !selected("child_reports_actions_after_a_guarded_return") {
        return;
    }
    run_trap_guarded(|| ()).expect("no trap");
    for (sig, name) in TRAP_SIGNALS {
        let action = installed_action(sig);
        let flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        println!(
            "{name} guard={} flags={}",
            action.sa_sigaction == trap_handler_address(),
            action.sa_flags & flags == flags
        );
    }
}

// spec: spec/12-runtime.md §12.7.6 — after a protected call returns, each trap
// signal's installed action is still the guard's, with `SA_SIGINFO` and
// `SA_ONSTACK`.
#[test]
fn guarded_return_leaves_the_guard_installed() {
    let end = test_child::run(&child("child_reports_actions_after_a_guarded_return"), &[]);
    assert_eq!(end.code, Some(0), "{}", end.stderr);
    let markers = TRAP_SIGNALS.map(|(_, name)| name);
    let lines = TRAP_SIGNALS.map(|(_, name)| format!("{name} guard=true flags=true"));
    assert_eq!(reported(&end.stdout, &markers), lines, "{}", end.stdout);
}

// --- Cell 3: unarmed default -----------------------------------------------

const UNARMED_SIGNAL: &str = "UNARMED_SIGNAL";

#[test]
fn child_traps_unarmed_after_a_guarded_call() {
    if !selected("child_traps_unarmed_after_a_guarded_call") {
        return;
    }
    let sig: libc::c_int = std::env::var(UNARMED_SIGNAL).unwrap().parse().unwrap();
    default_action(sig);
    run_trap_guarded(|| ()).expect("no trap");
    raise(sig);
    println!("SURVIVED");
}

// spec: spec/12-runtime.md §12.7.6 — with the guard installed and no extent
// armed, a trap is not the guard's: under a default previous action it kills
// the process by that signal. The `SIGFPE` leg separates a correct forward
// from a handler that jumps to a stale context, whose wild jump crashes with
// `SIGSEGV`.
#[test]
fn unarmed_trap_under_a_default_action_kills_by_the_signal() {
    for sig in [libc::SIGSEGV, libc::SIGFPE] {
        let end = test_child::run(
            &child("child_traps_unarmed_after_a_guarded_call"),
            &[(UNARMED_SIGNAL, &sig.to_string())],
        );
        assert_eq!(end.signal, Some(sig), "{}", end.stderr);
        assert!(!end.stdout.contains("SURVIVED"), "{}", end.stdout);
    }
}

// --- Cell 4: unarmed forward -----------------------------------------------

static FORWARDED_SIGNAL: AtomicI32 = AtomicI32::new(0);
static FORWARDED_INFO_SIGNO: AtomicI32 = AtomicI32::new(0);

extern "C" fn recording_handler(
    sig: libc::c_int,
    info: *mut libc::siginfo_t,
    _context: *mut libc::c_void,
) {
    FORWARDED_SIGNAL.store(sig, Ordering::SeqCst);
    if !info.is_null() {
        // SAFETY: a non-null `info` is the kernel's siginfo for this delivery.
        FORWARDED_INFO_SIGNO.store(unsafe { (*info).si_signo }, Ordering::SeqCst);
    }
}

#[test]
fn child_forwards_an_unarmed_trap() {
    if !selected("child_forwards_an_unarmed_trap") {
        return;
    }
    // SAFETY: a zeroed action with an empty mask and a valid `SA_SIGINFO`
    // handler is a well-formed `sigaction` argument.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = recording_handler as *const () as libc::sighandler_t;
        action.sa_flags = libc::SA_SIGINFO;
        libc::sigemptyset(&mut action.sa_mask);
        assert_eq!(
            libc::sigaction(libc::SIGSEGV, &action, std::ptr::null_mut()),
            0
        );
    }
    run_trap_guarded(|| ()).expect("no trap");
    raise(libc::SIGSEGV);
    println!(
        "forwarded sig={} info={}",
        FORWARDED_SIGNAL.load(Ordering::SeqCst),
        FORWARDED_INFO_SIGNO.load(Ordering::SeqCst)
    );
}

// spec: spec/12-runtime.md §12.7.6 — an `SA_SIGINFO` handler installed before
// the first guarded call is invoked, with its arguments, for an unarmed trap.
#[test]
fn unarmed_trap_is_forwarded_to_the_previous_siginfo_handler() {
    let end = test_child::run(&child("child_forwards_an_unarmed_trap"), &[]);
    assert_eq!(end.code, Some(0), "{}", end.stderr);
    let line = format!("forwarded sig={0} info={0}", libc::SIGSEGV);
    assert_eq!(
        reported(&end.stdout, &["forwarded "]),
        [line.as_str()],
        "{}",
        end.stdout
    );
}

// --- An unarmed trap during the install ---------------------------------

fn raise_fpe_after_its_install(sig: libc::c_int) {
    if sig == libc::SIGFPE {
        raise(libc::SIGFPE);
    }
}

#[test]
fn child_traps_unarmed_during_the_install() {
    if !selected("child_traps_unarmed_during_the_install") {
        return;
    }
    // SAFETY: installing `SIG_IGN` is always valid.
    unsafe { libc::signal(libc::SIGFPE, libc::SIG_IGN) };
    AFTER_HANDLER_INSTALL
        .set(raise_fpe_after_its_install)
        .unwrap();
    run_trap_guarded(|| ()).expect("no trap");
    println!("SURVIVED");
}

// spec: spec/12-runtime.md §12.7.6 — an unarmed trap delivered while the
// guard is still installing its handlers is forwarded to the action it
// replaced: an ignored signal stays ignored. The hook raises `SIGFPE` on the
// installing thread just after the guard's handler for it is in place.
#[test]
fn unarmed_trap_during_the_install_is_forwarded_to_the_replaced_action() {
    let end = test_child::run(&child("child_traps_unarmed_during_the_install"), &[]);
    assert_eq!((end.code, end.signal), (Some(0), None), "{}", end.stderr);
    assert_eq!(
        reported(&end.stdout, &["SURVIVED"]),
        ["SURVIVED"],
        "{}",
        end.stdout
    );
}

// --- Cell 5: nesting -------------------------------------------------------

#[test]
fn child_traps_in_an_outer_extent_after_an_inner_return() {
    if !selected("child_traps_in_an_outer_extent_after_an_inner_return") {
        return;
    }
    let outer = run_trap_guarded(|| {
        let inner = run_trap_guarded(|| 7);
        println!("inner: {:?}", inner);
        raise(libc::SIGSEGV);
    });
    println!("outer: {:?}", outer);
}

// spec: spec/12-runtime.md §12.7.6 — an inner protected call on one thread
// returns, and a trap in the outer extent is still recovered by the outer call.
#[test]
fn trap_after_a_nested_return_is_recovered_by_the_outer_call() {
    let end = test_child::run(
        &child("child_traps_in_an_outer_extent_after_an_inner_return"),
        &[],
    );
    assert_eq!((end.code, end.signal), (Some(0), None), "{}", end.stderr);
    let outer = format!("outer: Err(TrapSignal({}))", libc::SIGSEGV);
    assert_eq!(
        reported(&end.stdout, &["inner: ", "outer: "]),
        ["inner: Ok(7)", outer.as_str()],
        "{}",
        end.stdout
    );
}

// --- The signal-writer census ----------------------------------------------

const SIGNAL_WRITERS: [&str; 2] = ["libc::signal(", "libc::sigaction("];

fn signal_writer_sites(
    sources: &std::collections::BTreeMap<std::path::PathBuf, String>,
) -> std::collections::BTreeMap<String, usize> {
    let mut sites = std::collections::BTreeMap::new();
    for token in SIGNAL_WRITERS {
        for (site, count) in token_sites(sources, token) {
            *sites.entry(site).or_insert(0) += count;
        }
    }
    sites
}

// spec: design/intrinsics/process-lifecycle.md §1.8 — inside this crate, only
// the guard's one install and its default-action forward write a trap
// disposition. The planted leg proves the census detects a writer elsewhere.
#[test]
fn trap_dispositions_are_written_only_by_the_guard() {
    let mut sources = production_sources();
    // `current_action` passes a null new action: a query, not a write.
    let census = expected(&[
        ("io_guard.rs::current_action", 1),
        ("io_guard.rs::forward_unarmed_trap", 1),
        ("io_guard.rs::install_trap_handler", 1),
    ]);
    assert_eq!(signal_writer_sites(&sources), census);

    sources.insert(
        "planted.rs".into(),
        "fn planted() {\n    unsafe { libc::signal(libc::SIGSEGV, libc::SIG_DFL) };\n}\n".into(),
    );
    let mut planted = census.clone();
    planted.insert("planted.rs::planted".to_owned(), 1);
    assert_eq!(signal_writer_sites(&sources), planted);
}
