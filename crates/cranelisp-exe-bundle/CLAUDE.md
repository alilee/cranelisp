# cranelisp-exe-bundle — local conventions

The voice of the code: what the produced `libcranelisp_exe_bundle.a` must contain,
why the two force-link mechanisms differ, and the startup-ordering invariants a
`--link` binary depends on. Owned by `/dev` when narrow-deployed to this crate.

This crate is `crate-type = ["staticlib"]` (`Cargo.toml`). Its **entire job is
linker discipline**: it emits one `.a` that carries the Cranelisp runtime
(intrinsics + primitives + Rust `std`) so a standalone `--link` executable needs
no compiler installed. It has almost no logic — two `#[no_mangle]` startup hooks
and a wall of force-link `pub use`. The `--link` *orchestration* (startup-stub
emission, linker invocation, `.rlib` handling) lives in `src/exe.rs` +
`src/link/`, NOT here — see `design/backend/executable-generation.md` (§6 = this
bundle; §11–12 = the Linux ELF port and the `Linker` trait). Do not restate that
design here.

## Two force-link mechanisms, and why they differ (the load-bearing asymmetry)

The `.a` produced by a plain `staticlib` build contains only symbols this crate
*references*; the linker strips any `#[export_name]`/`#[no_mangle]` runtime symbol
nothing here names. Two DIFFERENT anchoring mechanisms keep the runtime alive, and
a reader will misread the asymmetry as inconsistency:

1. **Intrinsics — anchored by `pub use` re-exports** (`lib.rs:59-76`). Each
   `pub use cranelisp_intrinsics::{alloc,drop,io,ivar,layout,panic,rc,trace,
   heap_string,vec_runtime}` exists SOLELY to reference the submodule so its
   backend-emitted-call targets (alloc, RC, drop, IO trampoline incl.
   `cranelisp_run_io`, panic, trace) survive into the `.a`. **These are not dead
   code — deleting one silently strips its symbols and a `--link` binary faults at
   the first backend-emitted call to it.** (S66 W4a migrated them off the retired
   `cranelisp-runtime` shim onto terminal `cranelisp-intrinsics`; `trace` rejoined
   S76 / FIXME 0255 after the 2026-06-04 trace ruling made `(trace …)` work in
   `--link`; `layout` re-export = the `cranelisp_check_layout_hash` gate the
   backend declares `Linkage::Import` and never names in Rust.)

2. **Primitives — anchored by a startup hook, NOT re-exports.** The
   `pub use cranelisp_primitives::*` force-link lines were RETIRED S68 W3
   (Decision 0048 §Cascade). The replacement is `cranelisp_init_primitives()`
   (`lib.rs:100-103`): `LazyLock::force(&cranelisp_primitives::PRIMITIVES_TABLE)`.
   Forcing the static runs its init body, which takes every primitive fn ptr's
   address (`extern_shims()`), so the linker keeps them as transitive deps of a
   live static rather than via implicit `pub use` discipline (Principle 7 — the
   dependency is legible at the site that needs it). If a *primitive* vanishes
   from a `--link` binary, this hook or one of the three mechanisms in
   `crates/cranelisp-primitives/CLAUDE.md` §"DCE survival" regressed — do NOT
   re-add a `pub use` or a `#[used]` static to "fix" it.

## The `__cranelisp_got_primitives` link symbol + the null-slab crash window

The same `LazyLock::force` ALSO populates `PRIMITIVES_GOT_SLAB`, exported as
`__cranelisp_got_primitives` (FIXME 0280; the slab lives in `cranelisp-primitives`,
`lib.rs:143` there). Two facts a reader must hold together:

- **The export is what lets `ld` resolve `--link` extern-primitive dispatch.**
  Backend emits GOT-indirect against `__cranelisp_got_primitives` in ALL modes;
  a heap `GotTable` could never be a link-time symbol, so without the exported
  static slab `ld` fails "symbol not found: __cranelisp_got_primitives".
- **The slots are NULL until the hook runs — reading one before is a SIGSEGV.**
  So `cranelisp_init_primitives()` MUST execute before the first GOT-indirect
  dispatch. `cranelisp_init_platform` (`lib.rs:114-132`) calls it FIRST thing
  (`lib.rs:118`) for exactly this reason. FIXME 0280 also made the primitives
  call **unconditional**: pre-0280 it rode on `cranelisp_init_platform`, so a
  no-platform program calling an extern primitive reached user code with an
  unpopulated GOT. Full rationale: `design/arch/facades/int.md` §"Exe-bundle
  startup contract".

## `host_callbacks()` is single-sourced — do not hand-mirror (FIXME 0419)

`cranelisp_init_platform` builds its `HostCallbacks` via
`cranelisp_intrinsics::host_callbacks()` (`lib.rs:130`) — the ONE construction
site the JIT path (`src/platform.rs`) and this `--link` stub both call. Do NOT
inline a `HostCallbacks { .. }` literal here: the divergence it prevents is the
DEF-6 payload-vs-base `alloc` mismatch, which cannot recur while there is exactly
one literal. The manifest fn ptr arrives as `i64` (from `func_addr` in Cranelift
IR) and is `transmute`d to `extern "C" fn(*const HostCallbacks) -> PlatformManifest`.

## What the `.a` carries — and what it deliberately does NOT

- **In**: intrinsics symbols (mechanism 1), primitives + their GOT slab
  (mechanism 2), the two `#[no_mangle]` hooks defined here, and a Rust `std`
  subset (`std::process::exit`, the `System` allocator, etc. — pulled in
  automatically by `staticlib`).
- **Out — platform code.** `cranelisp-platform` is an `extern crate` dep
  (`lib.rs:82`) only so the contract types resolve; platform *manifests* are
  linked SEPARATELY as `.rlib`s (macOS `-force_load`) / extracted `.o`s (GNU
  `--whole-archive`) by the linker driver, not baked into this `.a`. See
  executable-generation.md §11.5.

## Known asymmetry a reader would misread as a bug: the crt-entry requirement

This `.a` embeds Rust `std`, whose `System` allocator calls `malloc`. On Linux,
glibc (TLS/`errno`/`malloc`/stdio) is initialised by `__libc_start_main`, called
by crt's `_start` — NOT by the dynamic loader. So a custom ELF entry that bypasses
crt runs with uninitialised glibc and the **first** `cons`/string/ADT allocation
SIGSEGVs on unset `TPIDR_EL0`. That is why the Linux `--link` path routes the
startup stub through C `main` (crt calls it) rather than a bespoke `_start`; macOS
is safe with a custom entry because dyld inits libSystem first. If someone
"simplifies" the Linux path to a custom entry and it crashes before any user code,
this is why — full analysis in executable-generation.md §11.3, not a bug in this
crate.

## Seam map, tests, and build/debug hooks

- **Structure**: one file, `src/lib.rs` (~130 lines), no submodules.
- **No `#[cfg(test)]` in-crate.** A force-link staticlib has nothing unit-testable
  in isolation (its correctness IS "the produced `.a` links and runs"). Behaviour
  is validated only end-to-end by the `--link` suite (`tests/`: `link::*`,
  `build_confidence::*`, `spec_platforms*`, `platform_errors`, linked
  `trace`/`cache`).
- **Build hook**: the `.a` is NOT built by the normal test build — run
  `cargo build -p cranelisp-exe-bundle` (→ `target/{debug,release}/`) before any
  link-mode test, and after touching this crate OR any force-linked dep, or the
  suite links a stale archive (piecemeal-build skew; see the Linux VM baseline
  memory). `find_bundle_lib` (`src/exe.rs`) locates it; `CRANELISP_BUNDLE_PATH`
  overrides the search for CI/custom layouts.
- **Debug**: a runtime symbol missing from a `--link` binary → check the three
  DCE mechanisms (`crates/cranelisp-primitives/CLAUDE.md`) before touching
  anything here. `CRANELISP_CODEGEN_TRACE=1` surfaces the startup stub's
  GOT-indirect emission when diagnosing a null-slot fault.
