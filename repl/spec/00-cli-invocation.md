> [REPL specification index](index.md)

## 0. CLI Invocation Modes

The `cranelisp` binary supports the following invocation modes:

The general invocation form is:

```
cranelisp [--run | --test | --link] [-o <path> | --output <path>] [--no-color] [--no-cache] [--priority-workers N] [--nice-workers N] [--agent | --no-agent] [target]
```

The optional positional `[target]` specifies the project root and entry module (see §0.5). Invocations in this section show options before the target; §0.5 governs where the target may appear. The mode flags (`--run`, `--test`, `--link`) and the modifier flags (`--no-color`, `--no-cache`, `--agent`, `--no-agent`) are boolean modifiers and take no parameter; `--priority-workers` and `--nice-workers` each take a numeric argument `N`. `-o <path>` and its long form `--output <path>` take a path argument (§0.2.1.1). Flags modify the behaviour applied to the resolved entry module.

The modifier and worker flags (`--no-color`, `--no-cache`, `--priority-workers`, `--nice-workers`, `--agent`, `--no-agent`) are detailed in §0.6. The agent flags (`--agent`/`--no-agent`) are REPL-only and behaviorally gated on the embedded-agent feature; see §0.6.1 and §17.

| Mode | Invocation | Description | Status |
|---|---|---|---|
| REPL | `cranelisp [target]` | Interactive REPL (default when no mode flag) | [Tested] |
| Run | `cranelisp --run [target]` | Compile and execute `main`, then exit | [Tested] |
| Test | `cranelisp --test [target]` | Compile, then automatically discover, run and report tests (§0.2.2) | [Tested+Neg] |
| Link | `cranelisp --link [target]` | Compile and produce a standalone executable (§0.2.1) | [Tested] |
| Version | `cranelisp --version` | Print version string and exit | Future — not implemented (errors `unknown flag` today); see §0.4 |
| Help | `cranelisp --help` | Print usage summary and exit | Future — not implemented (errors `unknown flag` today); see §0.4 |

> The synopsis above is the specified invocation form. There is **no** `--release` flag (it errors `unknown flag`), and `--version`/`--help` are not yet implemented (§0.4). The keep-this-consistent companion is `user/cli-reference.md` — the two MUST agree.

### 0.1 REPL Mode [Tested]

When invoked with no arguments, the binary MUST start the interactive REPL with cwd as the project root and `user` as the entry module: display the startup banner (see Section 6.2), load the prelude, and present the primary prompt. The REPL runs until the user enters `/quit` or sends EOF (Ctrl-D).

When invoked with a positional target (e.g. `cranelisp mymod`, `cranelisp dir/mymod`), the REPL MUST resolve the project root and entry module per §0.5 and start the REPL in that context. [R4 S52]

### 0.2 Run Mode (`--run`) [Tested+Neg tests/spec_10_io.rs::main_returning_io_string_exits_zero_run_and_linked, tests/spec_10_io.rs::run_mode_main_returns_pure_exit_code, tests/spec_10_io.rs::batch_main_pure_int_return_is_rejected, tests/repl_persist_race::repl_dep_load_no_race_with_persistent_workers — result handling (an `Int` inner value is the exit code, a non-`Int` inner value exits 0, a non-`IO` `main` fails compilation with a non-zero status naming `main` and `IO`) and REPL/`--run` parity of compile-and-call; the missing-`main`, missing-source-file and warnings-to-stderr clauses have no committed evidence]

`cranelisp --run [target]` MUST compile the module graph rooted at the resolved entry module, then call `main` in the entry module. The binary MUST NOT print any output itself — all output is produced by IO effects within the program. [R4 S52]

**Entry point resolution:**

1. The entry module MUST define a zero-argument function named `main`.
2. If `main` is not defined in the entry module, the binary MUST print an error to stderr and exit with status code 1. The error message MUST mention that `main` is required.

**Result handling.** `main` MUST have type `(Fn [] (IO _))` (`spec/10-io.md` §10.6). A `main` of any other type, including a bare `Int`, is a compilation failure (see below). `main` executes through the IO trampoline, so its side effects happen. If the inner result type is `Int`, that value is the process exit code; for any other inner type the exit code is 0.

**Warnings** MUST be printed to stderr. On compilation failure, the error MUST be printed to stderr and the process MUST exit with a non-zero status code.

If the resolved entry module source file does not exist, the binary MUST print an error to stderr and exit with status code 1.

### 0.2.1 Link Mode (`--link`) [R4 S52]

`cranelisp --link [target]` MUST compile the module graph rooted at the resolved entry module and produce a linked, standalone **executable**. It MUST NOT execute any code and MUST NOT produce output to stdout (beyond the `; Linking: …` progress line). [R4 S52]

**Parity with `--run`.** `--run` loads and executes the program; `--link`
produces a freestanding executable of the same program. Executing that
executable MUST produce exactly the same output as `--run` produces for the
program. The two modes provide the same language capabilities, including the
rejection of `discover-tests` references (§16.6); their execution and
optimisation strategies may differ. Parity concerns the output of executing the
program, not messages from compiling or linking it, such as warnings or the
`; Linking: …` line. [S122]

`--run` and `--link` MUST NOT be used together. If both are present, the binary MUST print an error to stderr and exit with status code 1.

#### 0.2.1.1 Output-Artifact Name and Location [S106]

**Name and location — the uniform rule [S106].** The output executable MUST
be named after the **entry (root) module's source-file stem** and MUST be written **into the same
directory as that module's source file** — not the project-directory name, not the current working
directory. One rule covers both the file-target and directory-project cases:

- **File target** (`dir/hello.cl`, or bare `mymod` resolving to `mymod.cl`): the entry module's
  source is `dir/hello.cl` / `mymod.cl`, so the artifact is `dir/hello` / `mymod` — the
  stem, beside the source. [S106]
- **Directory-project target** (§0.5.1 rule 3 — `cranelisp --link myproject`, where `myproject/`
  exists and no `myproject.cl` beside it, entry module `user`): the entry module's source is
  `myproject/user.cl`, so the artifact is `myproject/user` — the stem, beside the source. **Not**
  `myproject/myproject`, **not** `./user`. [S106]

On platforms with an executable suffix (Windows), the platform suffix applies:
`myproject/user.exe`, `dir/hello.exe`. [S106]

**`-o <path>` override (SETTLED [S106]):** an optional `-o <path>` flag sets the output path
explicitly, overriding the derivation above. This is the standard CLI escape hatch (`cc -o`,
`rustc -o`) for a user who wants the artifact somewhere specific. When `-o` is given, the resolved
path is used verbatim (relative paths resolved against cwd). [S106]

**`--output <path>` long form:** `--output <path>` is the long form of `-o <path>`. The two
spellings are equivalent: every requirement on `-o <path>` applies identically to
`--output <path>`. [Tested+Neg tests/link.rs::link_output_long_form_writes_named_path_not_default — the long form writes the artifact at the given path, verbatim against cwd, and the default `<stem>` is not written; short-form equivalence is unit-pinned at src/main.rs::tests::output_long_form_equals_short_form_in_any_position]

**Link-only output path (MUST):** `-o <path>` is accepted only together with `--link`,
the only mode that produces an artifact. In REPL, `--run` or `--test` mode, the binary MUST print
an error and the usage hint to stderr and exit with status code 1 (§0.3). [Tested tests/link.rs::run_with_output_path_is_rejected_with_usage_and_no_artifact, tests/test_runner.rs::test_mode_neg_combined_with_run_link_or_output_is_usage_error — the `--run` and `--test` legs: exit 1, the usage hint and no artifact; the REPL leg has no committed evidence]

**Collision-diagnostic floor (MUST) [S106]:** if the resolved
output path is an **existing directory**, the binary MUST emit a clear cranelisp diagnostic
naming the path (e.g. `error: output path 'user' is a directory — use -o <path> to choose a
different output`) and exit with status code 1, **rather than** surfacing a raw `ld`/`cc` linker
error. This floor holds independently of the name/location rule above — a directory collision must
never reach the user as an opaque toolchain error. [S106]

### 0.2.2 Test Mode (`--test`) [S122]

`cranelisp --test [target]` MUST compile the module graph rooted at the
resolved entry module (§0.5), then run the tests of every test module with the
test runner shared with `/run-tests` (§16.2). The program supplies no runner,
and a program that references `discover-tests` is refused (§16.6). [Tested+Neg tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests, tests/test_runner.rs::batch_modes_neg_refuse_uncalled_discover_tests_reference_with_one_diagnostic — result lines and summary identical to `/run-tests`; a `discover-tests` reference is refused]

**`main`.** `--test` MUST NOT call `main`, and the entry module need not
define it. A `main` that is present compiles as an ordinary definition; the
entry-point resolution and result handling of §0.2 do not apply. [Tested+Neg tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests, tests/test_runner.rs::test_mode_selects_exactly_the_import_chain_fresh_and_cached — a project with no `main` runs; a bare-`Int` `main` that panics if called is neither validated nor called]

**Test modules.** The test modules are the project modules in the entry
module's import chain: the entry module resolved from `[target]` (§0.5) and
every project module transitively reachable from it through that chain. [Tested+Neg tests/test_runner.rs::test_mode_selects_exactly_the_import_chain_fresh_and_cached, tests/test_runner.rs::test_mode_neg_chain_stops_at_library_modules_and_library_prelude — exact name sets on a fresh and a cache-restored run. Admitted: the entry, an `import` target, an `export`ed module, declared children with and without an import, and a project prelude. Excluded although compiled and on disk: alias-only, null-import and FQ-auto-loaded modules; a library module in a project lib directory, its child, a project module reachable only through it, and a lib-directory prelude. The default `{project_root}/stdlib/` classification is unit-pinned only, at src/session_v4/test_runner/selection/tests.rs::classifier_uses_the_resolution_tier_not_a_path_prefix]

- The chain runs from a module to:
  - each module named by an `import` or `export` entry whose names list is not
    empty (`spec/08-modules.md` §8.3, §8.4.0);
  - each submodule it declares with `(mod …)` or `(mod- …)` (§8.2.1, §8.2.3),
    whether or not it also imports that submodule; and
  - the prelude, through the implicit prelude import (§8.8.1).
- The chain does not run through a null import (§8.3.7), an alias-only import
  (§8.3.6), or a fully-qualified reference that auto-loads a module (§8.5.4).
  A module reached only in those ways is not a test module.
- The chain stops at library modules. A library module is not a test module,
  and the chain does not continue through its imports, exports or declared
  submodules, so a project module reachable only through a library module is
  not a test module. A prelude resolved from a lib directory is a library
  module and brings no tests into the run.
- A **project module** is one whose source file is resolved from the project
  root (`spec/08-modules.md` §8.11.1, §8.11.2 tier 2), or a submodule of a
  project module.
- A **library module** is one resolved from a lib directory
  (`spec/08-modules.md` §8.11.2 tier 3, §8.11.4), or a submodule of a library
  module. This holds even when the lib directory lies inside the project
  directory, such as the default `{project_root}/stdlib/`.
- Being compiled for the program does not make a module a test module. Test
  modules MUST NOT be found by searching the file system.

**Report.** The runner's report (§16.2) MUST be written to stdout. [Tested tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests]

**Exit status.** The process MUST exit with status 0 when no test failed or
panicked, including when no test is found, and with status 1 when any test
failed or panicked. [Tested+Neg tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests, tests/test_runner.rs::test_mode_selects_exactly_the_import_chain_fresh_and_cached, tests/test_runner.rs::test_mode_empty_run_reports_no_tests_found_and_exits_zero — 1 with a failure and a panic, 0 when every test passes and when none is found; a panic-only run is unit-pinned at src/session_v4/test_runner/run/tests.rs::report_text_and_exit_code_come_from_the_same_outcomes]

**Warnings** MUST be printed to stderr, including §16.1's warning for a
mis-typed test. [Tested tests/test_runner.rs::test_mode_runs_every_test_reports_fq_lines_and_matches_run_tests]

**Compilation failure.** On compilation failure, the error MUST be printed to
stderr, no test runs, and the process MUST exit with a non-zero status. [Tested+Neg tests/test_runner.rs::test_mode_neg_compile_error_runs_no_test]

**Mode combination.** `--test` MUST NOT be used together with `--run` or
`--link`. If either is present with `--test`, the binary MUST print an error
and the usage hint to stderr and exit with status code 1 (§0.3). [Tested+Neg tests/test_runner.rs::test_mode_neg_combined_with_run_link_or_output_is_usage_error]

Target resolution (§0.5), including the missing-source error of §0.5.5, and the
modifier and worker flags (§0.6) apply to `--test`; `-o`/`--output` is rejected
(§0.2.1.1). [Tested+Neg tests/test_runner.rs::test_mode_neg_missing_entry_file_errors_without_report, tests/test_runner.rs::test_mode_neg_combined_with_run_link_or_output_is_usage_error — the missing-source error and the `-o` rejection; parsing of the target, modifier and worker flags as for `--run` is unit-pinned only, at src/main.rs::tests::test_flag_parses_target_and_modifiers_as_run_does]

### 0.3 Error Handling [Tested tests/link.rs::run_with_output_path_is_rejected_with_usage_and_no_artifact — usage hint to stderr and exit 1 for one invalid-argument class (an output path without `--link`); unknown flags, `--run` with `--link`, and the hint's positional-target content have no committed evidence]

Invalid arguments (e.g., unknown flags, `--run` and `--link` together) MUST print a usage hint to stderr and exit with status code 1. The usage hint MUST show the supported invocation form including the positional target syntax.

### 0.4 Future: `--version` and `--help` [R4]

**Not yet implemented.** As built, `cranelisp --version` and `cranelisp --help` both error `unknown flag: --version` / `unknown flag: --help` (the usage hint to stderr) and exit with status code 1 — they are parsed like any other unrecognised flag (§0.3).

When implemented:

`cranelisp --version` SHOULD print the version string (format: `cranelisp <semver>`) to stdout and exit with status code 0.

`cranelisp --help` SHOULD print a usage summary listing all supported flags and their descriptions to stdout and exit with status code 0.

When added, they MUST follow standard CLI conventions (GNU-style long flags, stdout for informational output, exit code 0 on success).

### 0.5 Positional Target Resolution [R4 S52]

All invocation modes accept an optional positional `[target]` argument that specifies the **project root** and **entry module**. The target may appear before, after or between options. An option that takes a value keeps that value immediately after it. [Tested src/main.rs::tests::target_between_options_keeps_option_values_adjacent — parser unit only; no process-level cell spawns the target-first or between-options order]

#### 0.5.1 Resolution Rules

The target argument is resolved to a `(project_root, entry_module)` pair according to the following rules, applied in order:

1. **No target**: project root is cwd, entry module is `user`.
2. **Target has a directory component** (contains `/`): the directory portion is the project root, the final component is the entry module name. E.g. `dir/mymod` resolves to project root `dir/`, entry module `mymod`.
3. **Target is an existing directory with no same-named `.cl` file beside it** (no `/`, the name matches a directory in cwd, and `{target}.cl` does NOT exist in cwd): project root is that directory, entry module is `user`. E.g. if `myproject/` exists and `myproject.cl` does not, `cranelisp myproject` resolves to project root `myproject/`, entry module `user`.
4. **Target is a bare name** (no `/`; either no matching directory exists, or a same-named `{target}.cl` file exists beside the directory): project root is cwd, entry module is the target name. E.g. `cranelisp mymod` resolves to project root `.`, entry module `mymod`. **The file wins on ambiguity:** when both `mymod.cl` and `mymod/` exist in cwd, the entry resolves to the file `mymod.cl` (project root cwd), and `mymod/` holds its submodules. To force directory-as-project-root interpretation, name the directory explicitly (it cannot collide with a `.cl` file in that case).

The `.cl` extension MUST be optional in the target. `cranelisp user` and `cranelisp user.cl` MUST be equivalent. If the target ends in `.cl`, the extension MUST be stripped before deriving the entry module name.

The project root MUST be resolved to an absolute path. If a relative path is given, it MUST be resolved against cwd.

#### 0.5.2 Directory Component Detection

A target "has a directory component" when it contains at least one `/` separator. This includes:

```text
target           project root   entry module
dir/mymod        dir/           mymod
path/to/mymod    path/to/       mymod
./mymod          . (cwd)        mymod
../other/mymod   ../other/      mymod
```

A bare name like `mymod` does NOT have a directory component, even if a directory named `mymod` exists. The directory-existence check (rule 3) is a separate, lower-priority rule, and rule 3 only fires when there is no same-named `.cl` file beside the directory (the file wins on ambiguity — see §0.5.1 rule 4 and §0.5.5).

#### 0.5.3 Interaction with `--run` and `--link` [Tested tests/spec_10_io.rs::run_mode_main_returns_pure_exit_code — the options-first order `--run <target>` as a process; the target-first equivalence is unit-pinned at src/main.rs::tests::target_before_or_after_mode_flag_parses_identically for `--run` and `--link`, with no process-level target-first cell]

The `--run` and `--link` flags are boolean modifiers — they do not take parameters. The positional target is always resolved via §0.5.1 regardless of which mode flag is present. The target may appear before or after the flags: `cranelisp dir/mymod --run` and `cranelisp --run dir/mymod` MUST be equivalent.

#### 0.5.4 Examples [R4 S52]

| Invocation | Project root | Entry module | Notes |
|---|---|---|---|
| `cranelisp` | cwd | `user` | Default: REPL in current directory |
| `cranelisp user` | cwd | `user` | Explicit default module |
| `cranelisp user.cl` | cwd | `user` | `.cl` stripped |
| `cranelisp mymod` | cwd | `mymod` | Bare name, not a directory |
| `cranelisp myproject` | `myproject/` | `user` | `myproject/` is an existing directory, no `myproject.cl` beside it |
| `cranelisp app` (both `app.cl` and `app/` exist) | cwd | `app` | **File wins** — entry is `app.cl`; `app/` holds submodules |
| `cranelisp dir/mymod` | `dir/` | `mymod` | Directory component present |
| `cranelisp ./mymod` | cwd | `mymod` | Explicit cwd via `./` |
| `cranelisp ../other/app` | `../other/` | `app` | Relative parent path | <!-- doc-check: literal reason="Hypothetical CLI paths" -->
| `cranelisp --run` | cwd | `user` | Run mode, default target |
| `cranelisp --run mymod` | cwd | `mymod` | Run mode with target |
| `cranelisp --run dir/mymod` | `dir/` | `mymod` | Run mode with path |
| `cranelisp --link dir/mymod` | `dir/` | `mymod` | Link mode with path |

#### 0.5.5 Error Handling [R4 S52]

1. If the target contains a directory component and the directory does not exist, the binary MUST print an error to stderr naming the missing directory and exit with status code 1.
2. If the resolved entry module source file (`{project_root}/{entry_module}.cl`) does not exist:
   - In REPL mode: the binary SHOULD create an empty source file and proceed. This supports the common workflow of starting a new project from an empty directory.
   - In `--run` mode: the binary MUST print an error to stderr naming the missing file and exit with status code 1.
   - In `--link` mode: the binary MUST print an error to stderr naming the missing file and exit with status code 1.
   - In `--test` mode: the binary MUST print an error to stderr naming the missing file and exit with status code 1. [Tested+Neg tests/test_runner.rs::test_mode_neg_missing_entry_file_errors_without_report — the `--test` leg only; the `--run` and `--link` legs are open under ACT-1004]
3. If the target is ambiguous (e.g. both a file `mymod.cl` and a directory `mymod/` exist in cwd), **the file wins**: the target resolves to the entry module `mymod` (file `mymod.cl`) with project root cwd, and `mymod/` is treated as the directory holding `mymod`'s submodules (per `spec/08-modules.md §8.11`). This is the normal shape of a project whose entry file declares submodules with `(mod child)`. Rule 3 in §0.5.1 (directory-as-project-root) only fires when there is *no* same-named `.cl` file beside the directory.

#### 0.5.6 Dotted Module Paths [R4 S52]

The positional target supports only file-system paths (`/`-separated), not Cranelisp dotted module paths. To start the REPL in a submodule, use the file-system path:

| Intent | Correct | Incorrect |
|---|---|---|
| Module `app` in `myproject/` | `cranelisp myproject/app` | `cranelisp myproject.app` |
| Submodule `core.str` | `cranelisp core/str` | `cranelisp core.str` |

Dotted names (e.g. `core.str`) MUST be treated as a single module name, not as a path separator. If a user passes `core.str`, the binary resolves it as entry module `core.str` in cwd — which will fail if no file `core.str.cl` exists.

#### 0.5.7 Project-Root `Cranelisp.toml` Scaffold [S91]

When the REPL is invoked with a **project-root-directory target** — the §0.5.1 rule 3 case (`cranelisp myproject` where `myproject/` exists in cwd and `myproject.cl` does **not** exist beside it, resolving to project root `myproject/`, entry module `user`) — and that directory does **not** already contain a `Cranelisp.toml`, the REPL SHOULD scaffold a default `Cranelisp.toml` in the resolved project root. This is the `cargo new` / `git init` ergonomic: pointing the tool at a fresh project directory leaves behind a discoverable, editable configuration template. [S91]

This scaffold is **always safe by construction** because the lib-directory model is additive (`spec/08-modules.md §8.11.4`, settled S91): the resolved lib-dir set is the UNION of all sources, and a `Cranelisp.toml` `lib-dirs` value only ever **adds** paths — it can never suppress `CRANELISP_LIB`, the programmatic/CLI additions, or the `{project_root}/stdlib/` default. A scaffold that ships an empty or all-commented-out `lib-dirs` therefore changes resolution by exactly nothing; it cannot turn off a tier that an absent file would have used. (This is what dissolves the original §8.11.4 footgun — there is no replacing tier to trip over — and is the precondition that makes auto-scaffolding correct rather than a behaviour-changing side effect.) [S91]

##### Trigger condition [S91]

The scaffold MUST be created **only** in the §0.5.1 rule 3 case (explicit project-root directory, entry module `user`, no `{target}.cl` beside the directory). It MUST NOT be created in any other resolution case:

| Resolution case | Scaffold? | Why |
|---|---|---|
| Rule 1 — no target (cwd default) | **MUST NOT** | Writing `Cranelisp.toml` into an arbitrary cwd on every bare `cranelisp` launch would litter unrelated directories. The user did not point at a project. |
| Rule 2 — directory component (`dir/mymod`) | MUST NOT | The target names an entry *module* in a root, not a "treat this directory as a new project" gesture; no scaffold. |
| Rule 3 — project-root directory (`myproject`, `myproject/` exists, no `myproject.cl`) | **SHOULD** | The explicit project-root gesture — the intended trigger. |
| Rule 4 — bare entry-module name (file wins) | MUST NOT | Root is cwd; same litter concern as rule 1. |

##### Mode [S91]

The scaffold is a **REPL-mode-only** behaviour. In `--run` and `--link` mode the REPL MUST NOT scaffold a `Cranelisp.toml` (or write any file as a configuration side effect): a batch compile/link MUST NOT mutate the project tree as a side effect of compiling. The trigger gates on REPL mode **and** rule 3 together; both conditions MUST hold. [S91]

##### Notice [S91]

On a successful create, the REPL MUST emit a one-line notice in the existing bracketed-notification format (§14.3):

```
[created Cranelisp.toml]
```

The notice mirrors the `[updated: <file>]` / `[errors: <file>]` family and satisfies the self-documenting-REPL principle: the user is told the project root was recognised and a config template now exists to edit. The notice MUST appear at startup, before the first primary prompt (alongside the banner/startup notices), not deferred until the first evaluation. The `<file>` is the bare name `Cranelisp.toml` (the file always lives at the project root, so no path prefix is needed; consistent with §14.3's project-root-relative rendering). Silent-create is the rejected alternative — it leaves a file in the user's tree with no signal, which violates the self-documenting principle. [S91]

##### Safety and idempotence [S91]

The scaffold MUST observe the following invariants:

1. **Never overwrite.** If `{project_root}/Cranelisp.toml` already exists (as a file, symlink, or directory), the REPL MUST NOT write to it and MUST NOT emit the `[created …]` notice. An existing config is left byte-for-byte untouched. This makes the behaviour **idempotent**: a second launch on the same project root is a silent no-op. [S91]
2. **Never write outside the project root.** The file MUST be created at exactly `{resolved_project_root}/Cranelisp.toml` (the absolute path from §0.5.1). No parent-directory walk, no cwd write, no symlink-target escape. [S91]
3. **Graceful on a read-only / unwritable directory.** If the project root is not writable (permissions, read-only filesystem, etc.), the REPL MUST NOT fail the session launch. It SHOULD emit a single non-fatal warning to stderr naming the directory and the reason (e.g. `[warning: could not create Cranelisp.toml in <dir>: <reason>]`), then proceed to a normal REPL exactly as if no scaffold were attempted. A scaffold failure is never fatal — the config file is a convenience, not a requirement (the optional-prelude / empty-config principle). [S91]
4. **Benign on resolution.** Because the model is additive (above), a freshly-scaffolded default file MUST resolve identically to its absence — launching, scaffolding, and immediately re-resolving the lib path MUST yield the same lib-directory set as launching with no file at all. The scaffold is a pure documentation/template artefact, not a resolution change. [S91]

##### Scaffold content (cross-skill) [S91]

The literal byte content of the generated file and the file-writing mechanics are **not** part of this experience contract — they are owned by `/int` (the writer lives in `src/session_setup.rs`, beside `load_project_config_lib_dirs`; see `design/int/cranelisp-toml.md`). This section pins only the experience constraints the content MUST satisfy:

- The generated file MUST be valid TOML that parses without error (a self-inflicted malformed config would defeat the purpose).
- It SHOULD be a **teaching template**: a commented header naming the file's purpose, plus a **commented-out** `lib-dirs` example (and `platform-dirs`, §8.11.5) showing the schema — so the user sees the keys to uncomment, not an active `lib-dirs` that silently injects paths. Any *active* (uncommented) `lib-dirs` it ships MUST be limited to the directories the current resolution already contributes (e.g. echoing the live `CRANELISP_LIB` paths as commented examples), so invariant 4 (benign on resolution) holds. The recommended form ships **no active `lib-dirs` key** — all examples commented — which is trivially benign.

The §0.5.7 contract is the trigger + mode + notice + safety; `/int` owns what is written. [S91]

### 0.6 Modifier and Worker Flags

These flags modify behaviour but do not select a mode. They may appear in any mode (subject to the noted incompatibility) and in any position relative to the target.

| Flag | Argument | Effect | Default |
|---|---|---|---|
| `--no-color` | none | Disable ANSI colour in REPL and diagnostic output. | colour on |
| `--no-cache` | none | Bypass the on-disk module cache (recompile from source). **MUST error if combined with `--link`** (link mode relies on the object cache) — usage hint to stderr, exit code 1. | cache on |
| `--priority-workers` | `N` (numeric) | Number of priority compilation workers. A non-numeric `N` is an error (usage hint to stderr, exit code 1). | `1` |
| `--nice-workers` | `N` (numeric) | Number of background ("nice") compilation workers. A non-numeric `N` is an error. | `1` |
| `--agent` | none | Enable the embedded LLM agent for this session (REPL only). Requires the binary to be **built** with the agent feature AND a backend key present at runtime; otherwise the agent stays dormant (see §17.4). **MUST error on a binary built without the agent feature** (usage hint to stderr, exit code 1 — same style as `--no-cache` + `--link`) — the flag names a capability the binary does not have. | agent off |
| `--no-agent` | none | Force the embedded agent off for this session even when built-in and a key is present. **Always accepted** (a no-op on a non-agent build — asking for the agent off is trivially satisfied). | — |
| `--yes` (`-y`) | none | Autonomous-submit: auto-accept the agent's write-consent gates (Build form-submit, §17.14; Document preamble/docstring edit, §17.15) so the agent acts without the per-action `[y/N]` prompt. REPL only; meaningful only with an active agent. **MUST error on a binary built without the agent feature** (usage hint to stderr, exit code 1); a no-op when no agent is active on an agent-**capable** build. Auto-accepts **consent only**; the pre-flight validator (§17.14.3) still gates correctness. | off |

This table is kept consistent with `user/cli-reference.md`; the two MUST agree.

#### 0.6.1 `--agent` / `--no-agent` — Embedded Agent Toggle [S88]

The `--agent` and `--no-agent` flags are the runtime half of the agent's **opt-in-twice** discipline (§17.4). The embedded agent is a **dev-session capability only** — it is never part of `--run`, `--test` or `--link`, and never ships in a release artifact. Accordingly:

- `--agent` / `--no-agent` are meaningful **only in REPL mode**. In `--run`, `--test` or `--link` mode they MUST be accepted (not an error) and have **no effect** — the agent does not participate in batch compilation, test runs or linking. (This mode clause applies only on an agent-**capable** build; on a non-agent build `--agent` errors regardless of mode per the next bullet.) [S122]
- **`--agent` on a binary built WITHOUT the agent feature MUST be a hard error** (user ruling, 2026-07-09, S106). It MUST print a usage hint to stderr and exit with status code 1 — the **same error style** as `--no-cache` combined with `--link` (§0.6 table; §0.3): a short message naming the flag and the reason it is unsupported, e.g.
  ```
  error: --agent requires a binary built with the agent feature
  ```
  followed by the standard usage hint. This **reverses** the earlier accepted-no-op posture: the script-portability rationale (a script written for an agent-enabled build not breaking on a default build) does **not** apply — `--agent` names a capability the binary does not have, and silently ignoring it hides the mismatch. The binary MUST NOT print `unknown flag` (this is a *recognised* flag rejected for a *specific* reason, not an unknown token). [S106]
- **`--no-agent` on a binary built WITHOUT the agent feature stays an accepted no-op** — asking for the agent to be *off* is trivially true when the feature is compiled out, so it MUST NOT error and MUST NOT print `unknown flag`. With the feature compiled out, the agent is unconditionally absent; `--no-agent` is redundant-but-harmless. [S106]
- A binary **built with** the agent feature treats `--agent` as a request to enable the agent for the session and `--no-agent` as a request to keep it off. Even with `--agent`, the agent is **dormant** unless a backend key/config is also present at runtime (§17.4) — opt-in-twice. If `--agent` is given but no key is configured, the REPL SHOULD note at startup that the agent is built-in but dormant (no key), and `/ask` behaves per the dormant case (§17.1).
- When both `--agent` and `--no-agent` are present, `--no-agent` wins (the safe default — off).

The default with no flag is **agent off**, even on an agent-built binary with a key present: the user opts in explicitly per session. (An implementation MAY additionally honour a config-file or environment default; if it does, `--no-agent` MUST still override it to off.)

#### 0.6.2 `--yes` / `-y` — Autonomous-Submit Toggle [S89]

`--yes` (short form `-y`) is a **policy knob** that auto-answers the agent's write-consent gates. Per the `/arch` ruling (`design/arch/repl-embedded-agent.md §7.4`), it auto-*accepts* the consent question; it does **not** relocate, widen, or remove the gate, and it does **not** touch the pre-flight validator (§17.14.3) — it changes who answers the `[y/N]`, not whether code is validated. It is **off by default**: the human answers each write gate unless `--yes` is given. The flag is **blanket** — one `--yes` covers **both** agent write classes (Build form-submit, §17.14, *and* Document preamble/docstring edits, §17.15), following the universal `-y` convention. Accordingly:

- `--yes` / `-y` are meaningful **only in REPL mode** with an **active agent** (built `--features agent`, enabled per §0.6.1, and backed by a reachable provider — §17.4). **On a binary built WITHOUT the agent feature, `--yes`/`-y` MUST be a hard error** (user ruling, 2026-07-09, S106) — usage hint to stderr, exit code 1, the same `--no-cache` + `--link` error style as `--agent` (§0.6.1) — because there is no write-consent gate for it to auto-answer and the flag names an agent-only policy the binary cannot honour. It MUST NOT print `unknown flag`. **On an agent-capable build**, however, `--yes` remains an **accepted no-op** whenever no agent is *active* — in `--run`/`--test`/`--link` mode, or when the agent is dormant (no provider key) or disabled (`--no-agent`): the feature is present, so the flag is valid; there is simply no active gate to auto-answer. The reversal is scoped to the **feature-not-compiled-in** case only. [S106]
- **Precedence / interaction with `--agent`.** `--yes` presupposes the agent is in play but **does not itself enable the agent.** It is **not** an implicit `--agent`, and it does **not** bypass the opt-in-twice posture (§17.4): with no agent feature, no enabling flag, or no provider key, `--yes` stays a no-op — there is no write gate to auto-answer, so there is nothing to escalate. To act autonomously a user opts in explicitly: enable the agent (`--agent`, §0.6.1) **and** pass `--yes`. (`--no-agent` keeps the agent off, so `--yes` is likewise inert.)
- `--yes` auto-answers **consent, never validation.** The pre-flight validator (§17.14.3) runs on every submission regardless of `--yes`; only code that at least parses and type-checks ever reaches the session. `--yes` removes the question, not the correctness floor (§17.14.6).

When `--yes` is active and the agent first wants to write, the REPL MUST present a one-time first-use notice (§17.16) — the autonomy-escalation disclosure, sibling to the §17.8.1 transmit disclosure.

### 0.7 Execution Environment Variables [S93]

The `cranelisp` binary reads a small set of **environment variables** that tune execution outside the flag set. This subsection is the **normative home** for the *execution* knobs — the ones that affect how a program is scheduled and run in every invocation mode. They are part of the CLI contract on equal footing with the flags of §0.6, and `user/cli-reference.md` cross-links this table rather than originating the contract.

The execution knobs govern the runtime layer (the backend), so — unlike the REPL-only flags of §0.6 — they apply identically in **REPL, `--run`, and `--link`** modes. Each is read **once per process** (no per-evaluation re-read; an in-session `setenv` has no effect on an already-running binary). Both are **semantically invisible**: per `spec/12-runtime.md §12.4.3` (lenient evaluation / observational equivalence), neither changes what a program *computes* — only how the computation is scheduled. [S93]

| Variable | Effect | Default | Scope |
|---|---|---|---|
| `CRANELISP_SPARK_BUDGET=N` | Caps the number of concurrently in-flight lenient-evaluation **sparks** (parallel sub-computations) at `N`. `N=0` makes every spark create-gate take the direct arm ⇒ execution is **fully serial at the runtime layer**. A non-parsing / out-of-range value falls back to the default (it is never an error). | `4 × <worker-pool width>` (a small multiple of `rayon::current_num_threads()`) | Process-global; all modes [S93] |
| `CRANELISP_NO_LENIENT=1` | When set to **exactly** `1`, disables lenient evaluation entirely: nothing is marked sparkable, so evaluation is strictly **serial left-to-right** (the serial baseline — useful for measurement and debugging). Any other value (or unset) leaves lenient evaluation enabled. | unset (lenient evaluation **on**) | Process-global; all modes [S93] |

Both knobs ultimately produce the same user-visible effect — serial execution — but at different layers: `CRANELISP_NO_LENIENT=1` suppresses spark *emission* (no spark is ever created), while `CRANELISP_SPARK_BUDGET=0` suppresses spark *admission* at the runtime gate (sparks are emitted but every gate takes the direct arm). `CRANELISP_NO_LENIENT=1` therefore subsumes `CRANELISP_SPARK_BUDGET=0` for the serial-baseline use; the budget knob additionally allows a *bounded* (non-zero) degree of parallelism. [S93]

**Other `cranelisp` environment variables** have their normative homes elsewhere in this spec or in the language spec; this subsection is the execution-knob home and an index to the rest:

| Variable(s) | Purpose | Normative home |
|---|---|---|
| `NO_COLOR` | Suppress ANSI styling. | §10.1 |
| `CRANELISP_AGENT_PROVIDER`, `CRANELISP_AGENT_MODEL`, `CRANELISP_AGENT_KEY` / `ANTHROPIC_API_KEY`, `CRANELISP_AGENT_STUB_SCRIPT` | Embedded-agent provider/model/key configuration (dev-session, feature-gated). | §17.10.2 |
| `CRANELISP_AGENT_LOG` | Agent activity-log file sink (opt-in, feature-gated). | §17.20.2 |
| `CRANELISP_AGENT_TRACE` | Persistent full-content agent trace file sink (opt-in, feature-gated). | §17.21 |
| `CRANELISP_LIB`, `CRANELISP_PLATFORM_PATH` | Library / platform-DLL search paths. | `spec/08-modules.md §8.11` (+ `user/cli-reference.md` consolidated user-facing home) |

Trace/diagnostic-dump variables (e.g. `CRANELISP_CODEGEN_TRACE`, `CRANELISP_IO_TRACE`, `CRANELISP_SCHEDULER_TRACE`, `CRANELISP_RC_TRACE`, `CRANELISP_GOT_TRACE`, `CRANELISP_MODULE_TRACE`) are **internal developer instrumentation**, not part of the user-facing CLI contract, and are intentionally out of scope here. [S93]
