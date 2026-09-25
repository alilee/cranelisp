# Host IO entry and platform-DLL load orchestration

Int's host-side use of the IO runtime and its orchestration of platform-DLL
loading. The runtime seam is `design/intrinsics/reactor.md` §0. Result
ownership and exit codes are [result-owner.md](result-owner.md). The platform
contract is `design/arch/platform-interface.md`.

## 1. Running a program

- **One driver.** `--run`, the REPL and the linked stub all call the runtime's
  `cranelisp_run_program(code, is_io)`. It clears the error slot, calls the
  compiled code, drives an IO result to completion, releases the IO tree and
  reports the outcome. Int never reaches into the reactor.
  - `--run` enters through `CompilerSession::trampoline`.
  - The REPL enters through `pipeline::execute_compiled_expr`.
  - `cranelisp_run_io` is the catalog's `runtime/run_io` import, not a host
    entry.
- **`main`.** Before running, `exe::validate_main` requires `main` to be
  `(Fn [] (IO _))` (`spec/10-io.md` §10.6.1). It also refuses an unresolved
  return-type-polymorphic dispatch in `main`'s body. `--run` and `--link`
  share this gate.
- **Exit code.** An `Int` inner result is the exit code, and any other inner
  result exits 0. The rule has one predicate
  (`result_owner::result_is_exit_code`), which the linked stub bakes in as
  well.
- **REPL expressions.** An IO-typed expression is forced by the same driver.
  Its result displays the returned payload under the payload's own
  fully qualified type, as
  [REPL display §1.2.1](../../repl/spec/01-display-format.md#121-io-expression-results)
  requires. The driver unwraps `IO a` once and
  [result-owner.md](result-owner.md) owns the payload. A definition turn
  executes nothing. A runtime trap renders as `runtime error: …`.

### 1.1 REPL IO execution notice

- **One determinant.** `pipeline::execute_compiled_expr` reads IO-ness once
  from the expression's settled type. The same value selects driver forcing
  and, when true, writes the notice line to process stdout and flushes it
  immediately before the driver call. Notice and forcing cannot disagree, and
  the notice precedes every effect and any code the driver runs
  ([Principle 07](../arch/principles/07-single-source-of-truth.md),
  [Principle 24](../arch/principles/24-resolve-once.md)). The driver is
  runtime-owned, so the notice is not placed inside it
  ([Principle 02](../arch/principles/02-narrow-interfaces.md)).
- **A flushed write, not returned data.** The notice is ordered against
  output that platforms write to fd 1 during the driver call. Data returned
  after the call cannot precede that output, so the notice is exempt from the
  binary's rule that warnings are returned data (`src/CLAUDE.md`).
- **Text and style.** The REPL display module owns the notice text, rendered
  through the `styled::render` seam. The pipeline decides only when it is
  written.
- **REPL-only by construction.** `--run` and `--link` do not reach
  `execute_compiled_expr`, so batch output never contains the notice. There is
  no mode flag ([Principle 11](../arch/principles/11-single-pipeline-mode-parameters.md)).
- **Every executing REPL caller shows it.** This covers user turns, the EOF
  flush, `/time`, `/mem` and agent submissions, with no per-caller code. The
  agent's tool result and the recent-turn ring carry the formatted result
  only, so they contain neither the notice nor effect output. Turns that do not
  execute show no notice: definitions, introspection, compile errors and
  typecheck-only agent probes.
- **Accepted residual.** Degraded startup recovery re-drives a backing file
  through the eval path. A hand-edited file holding a top-level IO expression
  prints the notice alongside the effect output it already prints. A
  suppression flag would cost more than this risk.

## 2. Platform-DLL loading

### 2.1 Form routing

The frontend extracts `(platform …)` forms, and `process_form` routes each one
to `handle_platform` (`src/process_form/platform.rs`). A platform form in a
module whose path contains `.` returns without loading anything (§3, gap 1).

### 2.2 Search order

`src/platform.rs::resolve_platform_path` implements `spec/08-modules.md` §8.11.3:

1. A name containing `/` or ending in a DLL extension is an explicit path.
2. `{project_root}/platforms/`.
3. `{lib_dir}/platforms/` for each library directory.
4. Each platform directory ([cranelisp-toml.md §2](cranelisp-toml.md#2-directory-assembly)).

Each directory accepts `{name}.{ext}` and the Cargo name
`libcranelisp_{name}.{ext}`.

### 2.3 Load and ABI gate

`load_platform_dll` opens the DLL, reads its manifest through the
`cranelisp_platform_manifest_<name>` export with the host callbacks, and
finds its GOT slab and optional layout hash.

- **ABI gate.** `check_abi_version` refuses a manifest whose ABI version
  differs from `cranelisp_platform::ABI_VERSION` with
  `PlatformError::AbiVersionMismatch`. Int propagates the refusal and never
  loads such a DLL.
- **Name check.** `load_platform_checked` also checks that the declared name
  matches.

### 2.4 Registration

`register_platform_in_tc` wraps the DLL's GOT slab in place, without copying.
It then installs each function through `SymbolTable::install_platform`, with
the manifest index as the GOT slot, so calls are GOT-indirect.

- A signature that does not return `IO` is refused.
- A checked type with a free type variable is refused as a load error naming
  the platform and function (`int.md` §16.0).

### 2.5 Layout-hash gate

If the DLL's embedded layout hash differs from the host's regenerated hash,
the two modes act differently (`layout_hash_gate`):

- the REPL warns, names `/platform-schema`, and loads;
- `--run` and `--link` refuse with `PlatformError::LayoutHashMismatch`.

An empty host hash is accepted.

### 2.6 Retention and cache

The session keeps each loaded DLL handle in `kept_dlls`, so the wrapped GOT
stays mapped for the life of the session. A cache hit re-runs the same load
from the persisted declarations, and a failure is a cache miss
([int.md §7.1](int.md#71-cache-hit-flow-inside-register_module)).

## 3. Open gaps

These were read from source on 2026-09-25. Evidence status is stated per gap;
`qa` owns attribution.

1. **A non-entry platform form is silently ignored.** `spec/10-io.md` §10.9.1
   makes a `platform` form in a non-entry module a compile-time error. The
   source skips it with no diagnostic, and the test for the rule is missing.
