# REPL Experience Specification

Normative specification for the Cranelisp REPL user experience. A conforming REPL MUST satisfy all requirements tagged with the current ring or earlier.

While called repl, the repl experience encompasses the entire user experience from invoking the repl as well as its associated CLI invocation modes, exit codes, batch output format, and cache lifecycle.

## 0. CLI Invocation Modes

The `cranelisp` binary supports the following invocation modes:

The general invocation form is:

```
cranelisp [target] [--run | --link] [--no-color] [--no-cache] [--priority-workers N] [--nice-workers N] [--agent | --no-agent]
```

The optional positional `[target]` specifies the project root and entry module (see §0.5). The mode flags (`--run`, `--link`) and the modifier flags (`--no-color`, `--no-cache`, `--agent`, `--no-agent`) are boolean modifiers and take no parameter; `--priority-workers` and `--nice-workers` each take a numeric argument `N`. Flags modify the behaviour applied to the resolved entry module.

The modifier and worker flags (`--no-color`, `--no-cache`, `--priority-workers`, `--nice-workers`, `--agent`, `--no-agent`) are detailed in §0.6. The agent flags (`--agent`/`--no-agent`) are REPL-only and behaviorally gated on the embedded-agent feature; see §0.6.1 and §17.

| Mode | Invocation | Description | Status |
|---|---|---|---|
| REPL | `cranelisp [target]` | Interactive REPL (default when no mode flag) | [Tested] |
| Run | `cranelisp [target] --run` | Compile and execute `main`, then exit | [Tested] |
| Link | `cranelisp [target] --link` | Compile and produce linkable object file | [Tested] |
| Version | `cranelisp --version` | Print version string and exit | Future — not implemented (errors `unknown flag` today); see §0.4 |
| Help | `cranelisp --help` | Print usage summary and exit | Future — not implemented (errors `unknown flag` today); see §0.4 |

> The synopsis above is the as-built CLI. There is **no** `--release` flag (it errors `unknown flag`), and `--version`/`--help` are not yet implemented (§0.4). The keep-this-consistent companion is `user/cli-reference.md` — the two MUST agree.

### 0.1 REPL Mode [Tested]

When invoked with no arguments, the binary MUST start the interactive REPL with cwd as the project root and `user` as the entry module: display the startup banner (see Section 6.2), load the prelude, and present the primary prompt. The REPL runs until the user enters `/quit` or sends EOF (Ctrl-D).

When invoked with a positional target (e.g. `cranelisp mymod`, `cranelisp dir/mymod`), the REPL MUST resolve the project root and entry module per §0.5 and start the REPL in that context. [R4 S52]

### 0.2 Run Mode (`--run`) [Tested+Neg tests/repl_persist_race::repl_dep_load_no_race_with_persistent_workers]

`cranelisp [target] --run` MUST compile the module graph rooted at the resolved entry module, then call `main` in the entry module. The binary MUST NOT print any output itself — all output is produced by IO effects within the program. [R4 S52]

**Entry point resolution:**

1. The entry module MUST define a zero-argument function named `main`.
2. If `main` is not defined in the entry module, the binary MUST print an error to stderr and exit with status code 1. The error message MUST mention that `main` is required.

**Result handling by return type:**

| `main` return type | Behavior |
|---|---|
| `IO _` | Execute through the IO trampoline (side effects happen). The inner type determines the exit code per the exit code rules below. |
| `Int` | Use the value as the process exit code. |
| Any other type | Exit with status code 0. No output. |

**Exit code rules:**

- If the inner result type (after IO unwrapping) is `Int`, the value is used as the process exit code.
- For all other types, exit code is 0.

**Warnings** MUST be printed to stderr. On compilation failure, the error MUST be printed to stderr and the process MUST exit with a non-zero status code.

If the resolved entry module source file does not exist, the binary MUST print an error to stderr and exit with status code 1.

### 0.2.1 Link Mode (`--link`) [R4 S52]

`cranelisp [target] --link` MUST compile the module graph rooted at the resolved entry module and produce a linkable object file. It MUST NOT execute any code and MUST NOT produce output to stdout. [R4 S52]

`--run` and `--link` MUST NOT be used together. If both are present, the binary MUST print an error to stderr and exit with status code 1.

### 0.3 Error Handling

Invalid arguments (e.g., unknown flags, `--run` and `--link` together) MUST print a usage hint to stderr and exit with status code 1. The usage hint MUST show the supported invocation form including the positional target syntax.

### 0.4 Future: `--version` and `--help` [R4]

**Not yet implemented.** As built, `cranelisp --version` and `cranelisp --help` both error `unknown flag: --version` / `unknown flag: --help` (the usage hint to stderr) and exit with status code 1 — they are parsed like any other unrecognised flag (§0.3).

When implemented:

`cranelisp --version` SHOULD print the version string (format: `cranelisp <semver>`) to stdout and exit with status code 0.

`cranelisp --help` SHOULD print a usage summary listing all supported flags and their descriptions to stdout and exit with status code 0.

When added, they MUST follow standard CLI conventions (GNU-style long flags, stdout for informational output, exit code 0 on success).

### 0.5 Positional Target Resolution [R4 S52]

All invocation modes accept an optional positional `[target]` argument that specifies the **project root** and **entry module**. The target MUST be the last argument on the command line, after all flags.

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

- `dir/mymod` — project root `dir/`, entry module `mymod`
- `path/to/mymod` — project root `path/to/`, entry module `mymod`
- `./mymod` — project root `.` (cwd), entry module `mymod`
- `../other/mymod` — project root `../other/`, entry module `mymod`

A bare name like `mymod` does NOT have a directory component, even if a directory named `mymod` exists. The directory-existence check (rule 3) is a separate, lower-priority rule, and rule 3 only fires when there is no same-named `.cl` file beside the directory (the file wins on ambiguity — see §0.5.1 rule 4 and §0.5.5).

#### 0.5.3 Interaction with `--run` and `--link`

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
| `cranelisp ../other/app` | `../other/` | `app` | Relative parent path |
| `cranelisp --run` | cwd | `user` | Run mode, default target |
| `cranelisp mymod --run` | cwd | `mymod` | Run mode with target |
| `cranelisp dir/mymod --run` | `dir/` | `mymod` | Run mode with path |
| `cranelisp dir/mymod --link` | `dir/` | `mymod` | Link mode with path |

#### 0.5.5 Error Handling [R4 S52]

1. If the target contains a directory component and the directory does not exist, the binary MUST print an error to stderr naming the missing directory and exit with status code 1.
2. If the resolved entry module source file (`{project_root}/{entry_module}.cl`) does not exist:
   - In REPL mode: the binary SHOULD create an empty source file and proceed. This supports the common workflow of starting a new project from an empty directory.
   - In `--run` mode: the binary MUST print an error to stderr naming the missing file and exit with status code 1.
   - In `--link` mode: the binary MUST print an error to stderr naming the missing file and exit with status code 1.
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
| `--agent` | none | Enable the embedded LLM agent for this session (REPL only). Requires the binary to be **built** with the agent feature AND a backend key present at runtime; otherwise the agent stays dormant (see §17.4). Ignored — but accepted, not an error — by a binary built without the agent feature. | agent off |
| `--no-agent` | none | Force the embedded agent off for this session even when built-in and a key is present. Always accepted. | — |
| `--yes` (`-y`) | none | Autonomous-submit: auto-accept the agent's write-consent gates (Build form-submit, §17.14; Document preamble/docstring edit, §17.15) so the agent acts without the per-action `[y/N]` prompt. REPL only; meaningful only with an active agent. A no-op on default (non-`agent`) builds and when no agent is active — accepted, never an error. Auto-accepts **consent only**; the pre-flight validator (§17.14.3) still gates correctness. | off |

This table is kept consistent with `user/cli-reference.md`; the two MUST agree.

#### 0.6.1 `--agent` / `--no-agent` — Embedded Agent Toggle [S88]

The `--agent` and `--no-agent` flags are the runtime half of the agent's **opt-in-twice** discipline (§17.4). The embedded agent is a **dev-session capability only** — it is never part of `--run` or `--link`, and never ships in a release artifact. Accordingly:

- `--agent` / `--no-agent` are meaningful **only in REPL mode**. In `--run` or `--link` mode they MUST be accepted (not an error) and have **no effect** — the agent does not participate in batch compilation or linking.
- A binary **built without** the agent feature MUST accept `--agent` and `--no-agent` as recognised flags (so a script written for an agent-enabled build does not break on a default build) and treat them as no-ops. It MUST NOT print `unknown flag` for them. With the feature compiled out, the agent is unconditionally absent regardless of these flags.
- A binary **built with** the agent feature treats `--agent` as a request to enable the agent for the session and `--no-agent` as a request to keep it off. Even with `--agent`, the agent is **dormant** unless a backend key/config is also present at runtime (§17.4) — opt-in-twice. If `--agent` is given but no key is configured, the REPL SHOULD note at startup that the agent is built-in but dormant (no key), and `/ask` behaves per the dormant case (§17.1).
- When both `--agent` and `--no-agent` are present, `--no-agent` wins (the safe default — off).

The default with no flag is **agent off**, even on an agent-built binary with a key present: the user opts in explicitly per session. (An implementation MAY additionally honour a config-file or environment default; if it does, `--no-agent` MUST still override it to off.)

#### 0.6.2 `--yes` / `-y` — Autonomous-Submit Toggle [S89]

`--yes` (short form `-y`) is a **policy knob** that auto-answers the agent's write-consent gates. Per the `/arch` ruling (`design/arch/repl-embedded-agent.md §7.4`), it auto-*accepts* the consent question; it does **not** relocate, widen, or remove the gate, and it does **not** touch the pre-flight validator (§17.14.3) — it changes who answers the `[y/N]`, not whether code is validated. It is **off by default**: the human answers each write gate unless `--yes` is given. The flag is **blanket** — one `--yes` covers **both** agent write classes (Build form-submit, §17.14, *and* Document preamble/docstring edits, §17.15), following the universal `-y` convention. Accordingly:

- `--yes` / `-y` are meaningful **only in REPL mode** with an **active agent** (built `--features agent`, enabled per §0.6.1, and backed by a reachable provider — §17.4). In `--run` or `--link` mode, on a binary **built without** the agent feature, and whenever **no agent is active** (dormant or `--no-agent`), `--yes` MUST be accepted (not an error) and have **no effect** — consistent with `--agent` (§0.6.1). It MUST NOT print `unknown flag`.
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

## Design Principle

> **The REPL reinforces the syntax of the language.** Every output teaches the user how to write Cranelisp.

Output uses the `:Type value` format — the same colon-prefixed type annotation syntax used in the language itself. Names are always fully qualified to teach the module system. Constructors use `Type.Constructor` dot notation (valid input syntax per §1.4.4 of the language spec).

## 1. Display Format

### 1.1 Universal Output Format [Tested+Neg tests/repl_introspection::bare_primitive_type_int_displays_type_info, tests/repl_introspection::display_defn_with_docstring_uses_dash_separator]

All REPL output uses a unified format that mirrors Cranelisp type annotation syntax. The primary line is always:

```
:Type {value|name} ; {classification} - {docstring first line}
```

Where:
- `:Type` — the fully-qualified type (per §1.4), always present
- `{value|name}` — either a runtime value (for expression results) or a fully-qualified name (for definitions and lookups)
- `; {classification} - {docstring}` — optional comment suffix. The classification is the name of the defining special form (`defn`, `deftype`, `deftrait`, `defmacro`, `special form`, `impl`) or the symbol-class word `primitive` (used for builtins in the `primitives` module — see §4.1.7). The docstring is the first line of the symbol's documentation. If the symbol has no docstring, only the classification appears. If there is no classification (literal values), the comment is omitted entirely.

Builtins use the same dash form: `; {classification} - {docstring}` with classification `primitive` (e.g., `; primitive - Add`). The classification word `primitive` (rather than `defn`) is what distinguishes the host-implemented builtin from a user-defined function; the docstring suffix grammar is identical to `defn`/`deftype`/etc.

**Related symbols** appear as comment lines below the primary line. Each section names a relationship using language syntax, followed by unqualified symbol names (bare names, since these are in-scope symbols):

```
; {relationship}:
;  {symbol} {symbol} ...
```

Related symbol lists use the **same normative layout algorithm** as `/list` categories (§3.3 rules L0–L4); the layout MUST be byte-for-byte identical to `/list` for the same name set. [Tested repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical] Within each section, locally-defined symbols appear before imported symbols.

**Examples:**

```
user> 42
:primitives/Int 42

user> double
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2

user> Display
:core.str/Display ; deftrait - Format as string
; defn:
;  show
; impl:
;  Point
;  Bool Float Int List Vec

user> Color
:user/Color ; deftype
; match:
;  Red Green Blue

user> if
:(Fn [primitives/Bool a a] a) if ; special form - Conditional branch

user> +
:(Fn [:core.num/Num a :a] a) core.num/Num.+ ; deftrait - Addition operator
```

Not every symbol class has related symbols. Functions, constructors, literals, and primitives have only the primary line (plus optional docstring). Types, traits, macros, and modules have related symbol sections.

### 1.2 Expression Results [Tested]

An expression evaluation MUST display the result in the format:

```
:QualifiedType value
```

The type prefix is always fully qualified. The value portion uses the **canonical value display format** defined in [spec §12.9](../spec/12-runtime.md#129-value-display-format). This includes elision rules for large values — the REPL MUST apply the same elision thresholds as all other contexts that use the canonical format.

Examples:

| Example | Test |
|---|---|
| `:primitives/Int 3` | [Tested tests/repl_introspection::display_int_result] |
| `:primitives/Bool true` | [Tested tests/repl_introspection::display_bool_true] |
| `:primitives/Float 3.14` | [Tested tests/repl_introspection::display_float_result] |
| `:user/Color Color.Red` | [Tested tests/repl_introspection::display_int_result] |
| `:(user/Option primitives/Int) (Option.Some 42)` | [Tested tests/repl_introspection::display_int_result] |
| `:(Fn [a] a) <closure>` | [Tested tests/repl_introspection::display_int_result] |

**Ring 0**: `primitives/Int`, `primitives/Bool`, `primitives/Float`, nullary ADT constructors, non-capturing function values.
**Ring 1**: `primitives/String`, data ADT constructors, closures, `Vec`, `List`.

**Ring 4**: `IO` (trampoline executes the effect chain; result displayed as `:(IO InnerType) (IO.Pure inner_value)`, e.g. `:(IO primitives/Int) (IO.Pure 42)`). IO is an ADT and MUST follow the same `Type.Constructor` display format as all other ADTs per [spec §12.9](../spec/12-runtime.md#129-value-display-format).

**Ring 4**: `Trace` — displayed using the standard ADT format per [spec §12.9](../spec/12-runtime.md#129-value-display-format). The REPL does NOT auto-format trace trees — the raw ADT value is shown. Users who want a human-readable indented call tree SHOULD import `core.trace` and call `trace-show-tree`. [R4 S20]

### 1.3 Definition Results [Tested]

When the user enters a definition form, the REPL confirms the definition using the universal format (§1.1). The response follows the same per-class rules as bare symbol lookup (§4.1) — a definition is immediately followed by its lookup display.

```
user> (defn double "Multiply by 2" [x] (* x 2))
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2

user> (deftype Color Red Green Blue)
:user/Color ; deftype
; match:
;  Red Green Blue

user> (deftrait (Sizeable a) (size [:a] :Int))
:user/Sizeable ; deftrait
; defn:
;  size

user> (impl Sizeable Circle (defn size [c] ...))
impl user/Sizeable for user/Circle
```

A function definition MUST NOT display `<closure>` — the user defined a *named* function, not an anonymous closure. `<closure>` is reserved for anonymous function *values* (§1.2, §1.5).

| Requirement | Test |
|---|---|
| defn shows type + qualified name | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| polymorphic defn shows type vars | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| deftype shows qualified type name | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| deftrait shows trait name | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| impl shows `impl Trait for Type` | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| constrained fn shows inline constraints | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| overloaded fn shows all variants | [Tested tests/repl_introspection::display_overloaded_fn_shows_all_variants] |

**Ring 0**: function definitions, type definitions.
**Ring 2**: trait declarations, trait implementations, constrained functions.
**Ring 3**: macros.

### 1.4 Type Display [Tested]

Types MUST be displayed using Cranelisp type notation with fully-qualified names:

| Type | Display | Test |
|---|---|---|
| Primitive | `primitives/Int`, `primitives/Bool`, `primitives/Float`, `primitives/String` | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| Function | `(Fn [ParamType1 ParamType2] ReturnType)` | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| ADT (no args) | `user/Color` | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| ADT (with args) | `(user/Option primitives/Int)` | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| Type variable | lowercase letter: `a`, `b`, `c`, ... | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| Constrained variable | `:core.numerics/Num a` | [Tested tests/repl_negative::display_neg_type_always_qualified] |

Type names MUST always be fully qualified with their module path. Type variables are bare lowercase — they are not module-scoped.

Polymorphic type schemes MUST display quantified variables as consecutive lowercase letters starting from `a`. Constraints MUST appear inline on first occurrence of the constrained variable.

```
:(Fn [a] a) user/id
:(Fn [:core.numerics/Num a :a] a) core.numerics/+
```

### 1.5 Value Display

Values are runtime results and have no module scope. They are displayed bare.

| Type | Display | Ring | Test |
|---|---|---|---|
| `Int` | decimal integer (e.g., `42`, `-7`) | 0 | [Tested tests/repl_introspection::display_int_result] |
| `Bool` | `true` or `false` | 0 | [Tested tests/repl_introspection::display_bool_true] |
| `Float` | decimal float (e.g., `3.14`) | 0 | [Tested tests/repl_introspection::display_float_result] |
| `String` | `"contents"` with escapes | 1 | [Tested tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |
| Nullary constructor | `Type.Ctor` (e.g., `Color.Red`, `Option.None`) | 0 | [Tested tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |
| Data constructor (multi-ctor) | `(Type.Ctor field1 field2 ...)` (e.g., `(Option.Some 42)`) | 1 | [Tested tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |
| Data constructor (single-ctor, name matches type) | `(Ctor field1 field2 ...)` (e.g., `(Point 3 4)`) | 1 | [Tested tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |

| Closure | `<closure>` | 1 | [Tested tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |
| Vec | `[elem1 elem2 ...]` (empty: `[]`) | 1 | [Tested+Neg tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |
| List | generic ADT recursive form (e.g., `(List.Cons 1 (List.Cons 2 List.Nil))`; empty: `List.Nil`) | 1 | [Tested+Neg tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |
| Seq | generic ADT recursive form (e.g., `(Seq.SeqCons h <closure>)`); REPL MUST NOT force-evaluate the lazy tail | 2 | [Tested tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation] |

`Vec` is a compiler-seeded primitive type, so the REPL knows to render it as `[elem1 elem2 ...]`. `List` and `Seq` are stdlib types defined via `deftype`; the REPL renders them through the generic ADT recursive formatter (Type.Constructor + recursive field formatting). The MUST requirement for `Seq` is termination: the REPL displays the constructor and field shape without forcing the lazy tail thunk, so an infinite sequence does not hang the prompt.

> **Aspirational** (not currently required): A future revision MAY introduce a type-directed pretty-printer that recognises `List` and `Seq` and renders them as `(list elem1 elem2 ...)` and `(seq elem1 elem2 ... +more)` (forcing up to a small bound). This would require either (a) a display protocol/trait the stdlib opts into per type, or (b) compiler-seeded recognition of named types from a known stdlib path. No such protocol exists today, so the generic ADT form is normative. These forms are promoted to MUST only once the display-protocol mechanism lands — tracked by `design/arch/fixmes/0050-*.md` (owner `/int`, with `/arch` on the protocol and `/stdlib` on List/Seq opt-in).


ADT fields MUST be recursively formatted according to this table.

**Representation-flattening is invisible to display (R5).** A single-constructor ADT whose
sole field is a scalar (`Int`, `Bool`, `Float`, or another such value) is **value-representation
flattened** by the compiler — the value is stored as a bare unboxed word, with no heap object
or tag word. This is a codegen optimisation (`design/arch/ownership-inference.md` §6.3 R5); it
MUST have **no effect on display**. Such a value MUST render as the ordinary single-ctor
constructor form `(Ctor value)` — identical to its non-flattened sibling — with the scalar
field formatted per its own row above. The display MUST NOT leak the flattened representation
(a raw `<tag:N>` sentinel is a non-conformance) and MUST NOT crash (a `Float` field's bit
pattern MUST NOT be dereferenced as a pointer). A flattened ADT nested as a field of an outer
ADT MUST likewise recurse to its constructor form.

| Value | Display | Ring | Test |
|---|---|---|---|
| Single-ctor single-scalar-field ADT (R5-flattened), `Int` field, e.g. `(Box 99)` | `(Box 99)` — never `<tag:99>` | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_int_shows_constructor_form] |
| … `Bool` field, e.g. `(B true)` | `(B true)` — never `<tag:1>` | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_bool_shows_constructor_form] |
| … `Float` field, e.g. `(F 3.14)` | `(F 3.14)` — MUST NOT crash | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_float_does_not_crash] |
| R5-flattened ADT nested as a field of an outer ADT | recurses to `(Ctor value)`, e.g. `(Wrap (Box 5) 7)` | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_nested_field_shows_constructor_form] |

Value semantics (construct / match / extract) are unaffected by flattening and were always
correct — this note pins the **display** invariant so the representation stays invisible
[Tested tests/display_exact.rs::r5_value_layout_construct_match_extract_is_sound].

### 1.5.1 Bare Polymorphic Values — Type Display via Introspection [Tested+Neg tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata]

A **result-only-polymorphic value** is a value whose finalised type is polymorphic with no concrete instantiation forced by the surrounding context — e.g. a bare `None` (type `∀a. (Option a)`) or a bare empty literal `[]` (type `∀a. (Vec a)`) entered alone at the prompt. Such a value has **no concrete runtime representation** to show: under the slot⟺concrete model it is *slot-less* (`UserFnState::Polymorphic`) — it has no GOT slot and is not compiled as a runtime value.

| Requirement | Test |
|---|---|
| A bare/unpinned polymorphic value entered at the REPL MUST display its **polymorphic type** in `:Type value` form — fully-qualified type, constructor/value form. It MUST NEVER be an opaque error. | [Tested tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata, tests/repl_introspection::display_empty_vec_value] |
| Bare `None` MUST display `:(prelude/Option a) Option.None` form — the `Option.None` value form prefixed by the polymorphic `(…/Option a)` type. | [Tested tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata] |
| Bare `[]` MUST display the `(primitives/Vec a)` type prefix and the `[]` value form. | [Tested tests/repl_introspection::display_empty_vec_value] |
| The display MUST NOT render the symbol's *definition* drawer (e.g. `; deftype`, a module-qualified constructor path `fn.option/…`) — this is a value-display, not a definition lookup. | [Tested tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata] |

This is the **self-documenting-REPL principle applied to polymorphic values** (root `CLAUDE.md` §"Design Principles": "No valid language construct should produce an opaque error"). Because there is no concrete runtime value to show, the useful feedback the REPL gives back is the **type** — read from the symbol-table scheme via introspection — in the same `:Type value` notation every other result uses.

**Served from introspection, never from a slot.** The display MUST be served by reading the polymorphic scheme from the symbol table (introspection over the type), NOT by compiling, slotting, or evaluating the value to a concrete runtime representation. This is the architectural reason the disposition works for a slot-less `UserFnState::Polymorphic` def: a result-only-polymorphic value has no GOT slot and never reaches codegen, so the REPL cannot read a runtime value — it reads the *scheme* instead and renders the polymorphic type. An implementation that tries to compile/slot the bare value to display it would either fail (no slot) or force a spurious concretisation; the conforming path is type-display-by-introspection.

**Distinct from the §3.11 codegen-forced ambiguity error.** The language spec (`spec/03-types.md` §3.11) rejects an *ambiguous* polymorphic type — an unconstrained type variable that remains after inference — as a **type error**. That rejection applies only to a polymorphic value in a position that **actually reaches codegen** and must be monomorphised (e.g. a top-level value expression whose concrete instance the program demands but cannot determine). It does **not** apply to this REPL bare-display path: displaying a bare `None`/`[]` is pure introspection over the symbol-table scheme and never requires the value to have a GOT slot or to be compiled. The two dispositions are complementary, not contradictory — §3.11 governs *codegen* (where a residual `Type::Var` is a bug); §1.5.1 governs *REPL display* (where a residual `Type::Var` is exactly the useful feedback to show).

## 2. Prompt [Tested]

### 2.1 Primary Prompt [Tested tests/repl_lifecycle::boot_prompt_format_timing_and_module]

The primary prompt MUST display:

```
{compile_ms}+{eval_ms}ms; {module}>
```

Where:
- `compile_ms` — JIT compilation time of the previous expression (integer milliseconds)
- `eval_ms` — evaluation time of the previous expression (integer milliseconds)
- `module` — current module name (default: `user`)

On startup (before any expression), the timing SHOULD be `0+0ms`.


**Ring 0**: timing and prompt display.
**Ring 2**: module name changes when `/mod` switches namespace.

### 2.2 Continuation Prompt [Tested tests/repl_lifecycle::continuation_prompt_for_unclosed_paren]

When multi-line input is in progress (unmatched parentheses or brackets), the continuation prompt MUST be:

```
{spaces}...
```

Where `{spaces}` aligns the `...` with the start of user input on the primary prompt line.

### 2.3 Empty and Comment-Only Input [Tested tests/repl_introspection::empty_input_silent]

Blank lines (empty or whitespace-only) MUST silently re-prompt with no output. The REPL MUST NOT produce an error, evaluation result, or any visible output — it simply presents the next prompt.

Comment-only lines (lines where all non-whitespace content begins with `;`) MUST silently re-prompt with no output. Since `;` is the Cranelisp comment character, a line consisting entirely of comments carries no evaluable content.

This enables:
- Natural use of blank lines and comments as formatting in demo scripts and piped input
- Interactive users pressing Enter on an empty line without seeing an error
- Pasting code blocks that contain comment lines without spurious error output

**Ring 0**: empty and comment-only input handling.

## 3. Slash Commands

Slash commands provide introspection and navigation. All commands start with `/` and are NOT expressions — they are REPL-only features.

### 3.1 Command Inventory

Per-row annotations below indicate test coverage for each command. Ring 4 introspection commands (`/disasm`, `/time`, `/mod`, `/reload`) are legitimately pending. (`/mem` E2E coverage landed Sprint 58 Wave 5.)

| Command | Aliases | Description | Ring | Test |
|---|---|---|---|---|
| `/help` | `/h` | Show available commands and usage | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/sig <name>` | `/s` | Show signature with typed parameters (§3.8) | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/doc <name>` | `/d` | Show docstring (including builtins — see spec/appendix-a-builtins.md §A.5) | 0 | [R1] |
| `/type <expr>` | `/t` | Show type without evaluating | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/info <name>` | `/i` | Full details: type, classification, code size, compile time | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/source <name>` | — | Show original source text | 0 | [R4 S10] |
| `/sexp <name>` | — | Show parsed S-expression | 0 | [R4 S10] |
| `/ast <name>` | — | Show AST | 0 | [R4 S10] |
| `/clif <name>` | — | Show Cranelift IR | 0 | [R4 S10] |
| `/disasm <name>` | — | Show disassembled native code | 0 | [R4 S10] |
| `/list [prefix]` | `/l` | List definitions in current module | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/time <expr>` | — | Evaluate with timing breakdown | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/expand <form>` | `/e` | Macro-expand a form | 3 | [R3 S16] |
| `/mod [name]` | — | Switch module namespace | 2 | [R4 S10] |
| `/imports [module]` | — | Show imports and special forms; filter by source module | 0 | [Tested+Neg tests/repl_introspection::imports_lists_special_forms, tests/repl_introspection::imports_neg_no_primitives_leak_on_fresh_session] |
| `/exports <module>` | — | List a module's importable public symbols | 2 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/mem [expr]` | `/m` | Show allocation statistics (see §3.7) | 4 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/run-tests [module]` | `/rt` | Discover and run test functions (see §16) | 4 | [R4] |
| `/run-all-tests` | — | Run all tests in project (see §16) | 4 | [R4] |
| `/sh <cmd>` | — | Run a shell command (see §13) | 4 | [R4 S52] |
| `/refs <sym>` | — | List sites that reference a symbol (reverse query; LLM-free — see §17.6) | 4 | [S88] |
| `/tests-for <sym>` | — | List test functions that reference a symbol (reverse query; LLM-free — see §17.6) | 4 | [S88] |
| `/doc <module>` | `/d` | Read a module's preamble (module-level documentation — see §17.5); `/doc <name>` reads a definition docstring (§3.1, builtins) | 0 | [S88] |
| `/ask <text>` | — | The explicit agent door — routes `<text>` to the embedded agent **unconditionally**, bypassing the resolution-aware classifier (useful even for a *known* symbol's prose; see §17.1); prints "agent not built in" when the feature is off | 4 | [S88] |
| `/context <path>` | — | **Debug command** — write the agent's full **assembled** next-turn request (system primer, harvested context, tools, transcript, current turn) to `<path>` as readable text, **without calling the model** (works dormant/offline, no key; see §17.11); human-only, not an agent tool; prints "agent not built in" when the feature is off | 4 | [Tested+Neg tests/agent.rs::context_feature_off_prints_not_built_in, tests/agent.rs::agent_on_context_dumps_request_to_file_dormant] |
| `/syntax [topic]` | — | Core-language syntax cheat-sheet — bare `/syntax` lists topics, `/syntax <topic>` shows that topic's dense, verified-compiling content (see §17.17); a human REPL command **and** an agent pull-tool; LLM-free (a static curated asset, works with the agent absent) | 4 | [S90] |
| `/search <query>` | — | **Design-pinned S90 (re-pin), implemented later** — search **importable-but-unimported** symbols (reachable on the lib search path ∪ the project root) by **name OR scheme, exact OR partial** (see §17.19); a **normal default-build session facility** (not agent-gated); also reached by the agent via the ordinary pull | 4 | [S90 re-pin — design only] |
| `/quit` | `/q` | Exit REPL | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |

### 3.2 `/help` Output [Tested tests/repl_introspection::help_lists_commands]

`/help` MUST list all available commands with a brief description. The output MUST be organized by category:

```
Available commands:
  /help (/h)        Show this help
  /sig (/s) <name>  Show signature
  /doc (/d) <name>  Show docstring
  ...
```

Commands not yet available (due to ring) SHOULD be omitted or marked as unavailable.

### 3.3 `/list` — Module Definitions [Tested tests/repl_introspection::list_empty_session]

`/list` shows symbols **defined in the current module** — the user's own work. It does NOT show imports or special forms (those belong on `/imports`). Constructors are included alongside other symbols alphabetically.

**Scope rule:** `/list` MUST show only names created by definitions in the current module: `defn`, `deftype`, `deftrait`, `impl` (trait method definitions), `defmacro`. Imported names MUST NOT appear. [Tested+Neg tests/repl_introspection::list_empty_session] Special forms MUST NOT appear (they are always available and shown by `/imports`). [Tested+Neg tests/repl_introspection::list_neg_no_special_forms_category] Primitives (`add-i64`, etc.) MUST NOT appear when the current module is `user`. [Tested+Neg tests/repl_introspection::imports_neg_no_primitives_leak_on_fresh_session]

**Categories:**

| Category | Contents | Ring | Test |
|---|---|---|---|
| Modules | Declared submodules | 2 | [R4 S15] |
| Macros | Macro definitions (`defmacro`) | 3 | [Tested+Neg tests/repl_introspection::list_empty_session] |
| Traits | Trait declarations (`deftrait`) | 2 | [Tested tests/repl_introspection::list_empty_session] |
| Types | User-defined types and constructors (`deftype`) | 0 | [Tested+Neg tests/repl_introspection::list_empty_session] |
| Fns | User-defined functions, trait method implementations, and field accessors | 0 | [Tested tests/repl_introspection::list_empty_session] |

Category order: Modules, Macros, Traits, Types, Fns. Empty categories are omitted. [Tested+Neg tests/repl_introspection::list_empty_session]

**Field accessors — canonical qualified form (`Type.field`).** Each field of a `deftype` produces a field accessor. Under the field-accessor model (`spec/05-definitions.md §5.2.6`, `spec/08-modules.md §8.5.2`), the accessor's **canonical** name is the qualified `Type.field` form (e.g. `Box.v`): a real, Public definition that `/list` MUST display under **Fns**, using the qualified `Type.field` form — consistent with the REPL's qualified-display convention (`:primitives/Int`, `:(Fn [a] a) user/id`; the §"Design Principle" rule that names are always fully qualified to teach the module system). [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]

The **bare** field name (e.g. `v`) is a **convenience alias** to the canonical accessor — it resolves when unambiguous and is an ambiguity error when two in-scope types share the field name. The bare alias is **NOT separately listed** by `/list` (option A — show canonical only): listing both `Box.v` and a bare `v` would double-count every field, and the bare alias is import-class (an alias into the current scope), so it falls under the existing "imported/alias names MUST NOT appear on `/list`" scope rule above. `/list` shows the canonical accessor exactly once, under its `Type.field` name. [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]

**Empty module:** When no definitions exist in the current module, `/list` MUST print `(no definitions)`. [Tested tests/repl_introspection::list_empty_session] This distinguishes "command worked on empty module" from a failed command.

**Negative requirements** (what MUST NOT appear): [Tested+Neg]

- No category should contain imported names (those belong on `/imports`) [Tested+Neg tests/repl_introspection::list_empty_session]
- No category should contain special forms (those belong on `/imports`) [Tested+Neg tests/repl_introspection::list_empty_session]
- No category should contain compiler-internal symbols (`__macro_*`, `$`-mangled names) [R4 S15]
- Constructors MUST appear in Types, not in Fns [Tested+Neg tests/repl_introspection::list_empty_session]
- A field accessor MUST appear only once, under its canonical `Type.field` name; the bare-field alias (`v`) MUST NOT appear as a second, separate accessor entry [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]

**Filter argument:** `/list <text>` performs a case-insensitive prefix match on symbol names across all categories, showing matching symbols with full type info. [Tested tests/repl_introspection::list_prefix_filter_matches_names] `/list` with no argument shows all definitions. [Tested tests/repl_introspection::list_empty_session]

**Large category display layout algorithm** [Tested+Neg repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical]**.** The multi-column line-breaking layout below is a **normative MUST**, not advisory. It is a deterministic, exactly-reproducible contract — the same input symbol set MUST always produce byte-for-byte identical output. Because this layout is **shared verbatim** by `/list` (§3.3), `/imports` (§3.4), `/exports` (§3.5), and related-symbol lists (§2, repl/spec.md:198), divergence between any two of those commands is a conformance defect, not a stylistic variation. Each rule below is individually checkable.

The layout is a **MUST** (not SHOULD) so that exact output can be asserted in tests and so the four commands stay mutually consistent. Each numbered rule is a separate conformance obligation:

- **L0 — Single-line threshold (the <7 case).** A category with **fewer than 7 names** MUST be rendered on a single line after the category label, space-separated, with no line-breaking applied. The breaking rules L1–L4 MUST NOT be applied below the 7-name threshold. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::list_layout_l0_under_seven_single_line, tests/repl_introspection.rs::list_layout_l0_neg_exactly_six_not_broken]

- **L1 — 7-or-more triggers breaking.** A category with **7 or more names** MUST apply the line-breaking layout (rules L2–L4). The threshold is exactly 7: 6 names stay on one line (L0), 7 names break. [Tested repl/spec.md→tests/repl_introspection.rs::list_layout_l1_seven_triggers_break]

- **L2 — Operators first, on their own break.** Non-alphabetic symbols (operators such as `+`, `-`, `*`, `!=`, `<=`) MUST be displayed before all alphabetic names, wrapping at 6 per line. After the last operator, a new line MUST start: an operator MUST NEVER share a line with an alphabetic name. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::list_layout_l2_operators_first_own_line, tests/repl_introspection.rs::list_layout_l2_neg_operator_never_shares_name_row]

- **L3 — Letter groups never split; early-break to stay together.** Alphabetic names MUST be grouped by first letter (case-insensitive) and the groups emitted in sorted order. Before appending a letter group to the current row, if `current_count + group_size > 6` the current row MUST be flushed first. A letter group MUST therefore appear either entirely on the current row (alongside earlier groups) or starting on a fresh row — it MUST NEVER be split across a row boundary, **except** when the group alone has 7+ names (then L4 applies). [Tested+Neg repl/spec.md→tests/repl_introspection.rs::list_layout_l3_letter_group_early_break, tests/repl_introspection.rs::list_layout_l3_neg_no_group_straddles_row]

- **L4 — Hard wrap at 6 within an oversized group.** A single letter group with **more than 6 names** MUST wrap at 6 names per line within itself. [Tested repl/spec.md→tests/repl_introspection.rs::list_layout_l4_oversized_group_wraps_at_six]

The example below is illustrative of the rules above; it is the reference layout that tests assert as expected output.

```
Fns:
  + - * / < > <= >= !=
  abs add ceil concat
  double drop
  empty? even? filter floor fold
  get
  ...
```

### 3.4 `/imports` — Imports and Special Forms [Tested+Neg tests/repl_introspection::imports_lists_special_forms]

`/imports` shows everything available in the current module that was NOT defined here: imported names and language special forms. This is the complement of `/list` — together they cover all symbols in scope.

**Categories:**

| Category | Contents | Ring | Test |
|---|---|---|---|
| Special forms | `if`, `let`, `fn`, `defn`, `deftype`, `match`, etc. | 0 | [Tested tests/repl_introspection::imports_lists_special_forms] |
| Macros | Imported macro definitions | 3 | [R4 S15] |
| Traits | Imported trait declarations | 2 | [R4 S15] |
| Types | Imported types and constructors | 0 | [R4 S15] |
| Fns | Imported functions and trait methods | 0 | [Tested tests/repl_introspection::imports_lists_special_forms] |

Category order: Special forms, Macros, Traits, Types, Fns. Empty categories are omitted (except Special forms, which are always present). [Tested tests/repl_introspection::imports_lists_special_forms]

**Format:** Each category lists names using the **same normative layout algorithm** as `/list` (§3.3 rules L0–L4) — names only, no type signatures. The layout MUST be byte-for-byte identical to what `/list` produces for the same name set (one shared formatter, not a re-implementation). Type the symbol name for more detail. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical, tests/repl_introspection.rs::list_layout_neg_names_only_no_type_sigs]

**Source module filter:** `/imports <module-name>` filters to show only imports from that source module (exact match). [Tested tests/repl_introspection::imports_lists_special_forms] Names are grouped under `From <module>:` and sorted alphabetically. Source modules sorted alphabetically.

```
user> /imports prelude
From prelude:
  + - * / < > <= >= != =
  case cond
  show str
  ...
```

**Unfiltered mode:** `/imports` with no argument shows all imports organized by category (not by source module). [Tested tests/repl_introspection::imports_lists_special_forms] This gives a quick overview of what's available. Use `/imports <module>` for per-module detail.

**Re-export provenance:** When the user writes `(import [prelude [*]])` and the prelude re-exports `+` from `core.numerics`, `/imports prelude` shows `+` under `From prelude:` — because that is the module the user imported from. The ultimate origin is available via `/info +` (§3.6).

**Reexport entries:** Both `Import` and `Reexport` module entries MUST be included. [Tested tests/repl_introspection::imports_lists_special_forms] A symbol re-exported through the prelude is still an import from the user's perspective.

**Glob imports:** When `(import [mod [*]])` was used, `/imports` MUST show the individual names that were imported (the expansion of `*` at the time the import was evaluated), not just `*`.

**Implicit prelude import (Ring 3+):** The compiler injects an implicit `(import [prelude [*]])` for all non-prelude modules (spec §8.8.1). This implicit import IS visible in `/imports` — the user needs to discover what the prelude provides.

**No imports:** In a fresh session with no explicit `(import ...)` and no prelude, `/imports` MUST show only Special forms. [Tested+Neg tests/repl_introspection::imports_lists_special_forms, tests/repl_introspection::imports_neg_no_primitives_leak_on_fresh_session] The `primitives` module's implicit availability is via the module resolution fallback, NOT via import — so primitives do not appear in `/imports` unless explicitly imported.

**Error cases:**
- `/imports nonexistent` — no imports from that module; silent re-prompt (not an error) [Tested+Neg tests/repl_introspection::imports_lists_special_forms]

### 3.5 `/exports <module>` — Module Public API [Tested tests/repl_introspection::exports_no_arg_shows_usage]

`/exports <module>` resolves a module and lists its importable (public) symbols. This answers "what can I import from this module?" before writing an `(import ...)` form.

**Argument:** The module name is required. `/exports` with no argument MUST print a usage hint: `Usage: /exports <module-name>`. [Tested tests/repl_introspection::exports_no_arg_shows_usage]

**Module resolution:** The argument is resolved using the same resolution logic as `(import [module [...]])` — submodule paths, root modules, and stdlib modules. If the module is not yet loaded, it SHOULD be resolved and loaded (same as an import would trigger). If the module cannot be found, print an error: `Module '<name>' not found`. [Tested tests/repl_introspection::exports_no_arg_shows_usage]

**Output format:** Public symbols listed by category — names only, no type signatures. [Tested tests/repl_introspection::exports_no_arg_shows_usage] Categories use the **same normative layout algorithm** as `/list` (§3.3 rules L0–L4); the layout MUST be byte-for-byte identical to `/list` for the same name set. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical, tests/repl_introspection.rs::list_layout_neg_names_only_no_type_sigs] Type the symbol name for more detail.

```
user> /exports math
Module 'math':
Fns:
  bar foo
```

Categories follow the same order as `/list`: Modules, Macros, Traits, Types, Fns. Names sorted alphabetically within categories.

**What counts as public:** Definitions with public visibility — `Def`, `Constructor`, `TraitDecl`, `TypeDef`, `Macro`. Import and Reexport entries in the target module are NOT shown (those are the module's own imports, not its exports).

**Field accessors in `/exports`.** A module's field accessors are public definitions and MUST be listed by `/exports` under their **canonical qualified `Type.field`** form (e.g. `Box.v`) — the same canonical/alias rule as `/list` (§3.3, "Field accessors — canonical qualified form"): the canonical accessor is the real Public `Def` shown by `/exports`; the bare-field name (`v`) is a convenience alias (import-class) and is NOT separately listed (option A — show canonical only), consistent with the "Import and Reexport entries are NOT shown" rule above. A field accessor appears in a module's exports exactly once, under its `Type.field` name. [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]

**Empty module:** If the module has no public symbols, print `Module '<name>' has no public symbols`. [R4 S15]

**Filter argument:** `/exports <module> <prefix>` performs a case-insensitive prefix match within the module's exports. [R4 S15]

### 3.6 `/info` Output [Tested tests/repl_introspection::info_resolves_trace_special_form]

`/info <name>` MUST display multi-line details using the `:Type name` format:

```
:(Fn [primitives/Int] primitives/Int) user/double
  (defn double [x] (* x 2))
  48 bytes, 2ms
```

For overloaded functions, all variants MUST be listed. For constrained functions, specializations MUST be shown.

For a symbol broken by a redefinition cascade, `/info` (and `/sig`) display broken status + provenance per §18.4. [S101]

### 3.7 `/mem` — Allocation Statistics [Tested]

`/mem` reports the runtime allocation counters maintained by `cranelisp-runtime`: total allocations observed, total deallocations, and bytes currently live. The command has two shapes — a **snapshot** (no argument) and a **delta** (with an expression argument). Both are comment lines (`;`-prefixed), consistent with the self-documentation convention in §1.5.

**Snapshot — `/mem`** — MUST emit two comment lines:

```
user> /mem
; live: <bytes> bytes (<live-allocs> allocations)
; allocs: <total-allocs>  deallocs: <total-deallocs>
```

- `<bytes>` is `cranelisp_runtime::bytes_current()` — sum of currently-live heap allocations in bytes.
- `<live-allocs>` is `allocs - deallocs` — the number of allocations that have not been freed.
- `<total-allocs>` and `<total-deallocs>` are the cumulative counters since process start.

The two fields between `allocs:` and `deallocs:` are separated by two spaces. The `(<live-allocs> allocations)` group is singular or plural depending on count (the implementation MAY always use `allocations` for simplicity).

**Delta — `/mem <expr>`** — MUST evaluate the expression, print its formatted result on the first line (per §1.2), then emit one comment delta line:

```
user> /mem (list 1 2 3)
:(collections.list/List primitives/Int) (List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))
; delta: allocs +<d-allocs>  deallocs +<d-deallocs>  bytes <±d-bytes>  live <±d-live>
```

- `<d-allocs>`, `<d-deallocs>` are non-negative deltas (prefixed `+`).
- `<d-bytes>` and `<d-live>` are signed deltas (`+`/`-`) because rebinding `it` can release previously-live allocations, making the delta negative.
- Each field is separated from the next by two spaces.

Evaluation errors MUST still emit the delta line — observation is the point, and a failed allocation is itself interesting data. The header line in the error case uses the standard §5 error format.

`/mem` MUST NOT start the runtime; the counters are valid from process start. An empty runtime reports `; live: 0 bytes (0 allocations)` and `; allocs: 0  deallocs: 0`.

| Requirement | Test |
|---|---|
| snapshot emits live + totals | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |
| delta prints result then delta line | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |
| signed `bytes` and `live` deltas | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |
| baseline counters at process start are zero | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |
| `/m` short alias produces snapshot | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |

### 3.8 `/sig` Output — Same Primary Line as Bare Lookup [S102]

`/sig <name>` shows the symbol's signature. Its output is not a separate format: the
primary line(s) `/sig` prints MUST be **byte-identical** to the primary line(s) a bare
lookup of the same name prints (§1.1 universal format, §4.1 per-class rules) —
fully-qualified type per §1.4, fully-qualified symbol name, and the same
`; {classification} - {docstring}` drawer. For overloaded functions and macros, `/sig`
prints the same per-variant / per-clause signature lines as bare lookup (§4.1.1, §11.2.3).
On a broken symbol, the §18.4 provenance comment line follows, identical to bare lookup's
(§18.4). [S102]

```
user> /sig double
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2
```

Unqualified type names or an unqualified symbol name in `/sig` output are non-conformances
(root `CLAUDE.md` §Design Principles — `:Type value` notation with fully-qualified names):
`:(Fn [Int] Int) double ; defn` is wrong in both positions. [S102]

> Arbitration record (FIXME 0492, S102): the short-form rendering the binary produces today
> was ruled an implementation defect, not a spec defect — every governing display rule
> (§1.1, §1.4, §4.1, §11.2.3, §17.18.1, §18.4) already mandated the fully-qualified form;
> this section makes the `/sig`-specific consequence explicit. Fix owner: `/int`
> (`repl.rs` `handle_sig` display seam).

| Requirement | Test |
|---|---|
| `/sig` primary line is byte-identical to bare lookup's (FQ type + FQ name + drawer) | [S102 — guard tests/repl_redefinition.rs::sig_broken_symbol_primary_line_matches_bare_lookup_fully_qualified, failing-not-ignored until the /int fix (FIXME 0492)] |

### 3.9 `/mod` — Namespace Switch and Turn-Environment Parity [S102]

`/mod [name]` switches the active module namespace. Its interactive behaviour — the prompt
changes to the new module, no confirmation is printed, bare `/mod` returns to `user`, an
unknown module gives an actionable error — is specified by the §8 module scenarios; this
section pins the **compilation-environment** contract, which is the load-bearing invariant for
the file-backed dev loop (`/mod M` + a defining form, editing a module in place).

**Turn-environment parity (MUST).** A form entered in a module-namespace turn (`/mod M`
followed by a `defn`/`deftype`/expression) MUST compile in the **same environment the module
`M`'s file body was compiled in**. Concretely, all of the following MUST be in scope for that
turn exactly as they are when `M`'s `.cl` file is loaded:

- the **implicit prelude values** — the prelude-provided operators and functions (`+`, `-`,
  `show`, …) are available as bare names (spec `08-modules.md` §8.8.1's implicit
  `(import [prelude [*]])`); [S102]
- the **prelude type aliases** — a bare `:Int` annotation resolves to `:primitives/Int` in the
  turn's forms exactly as in the file body (spec `08-modules.md` §8.9.1); [S102]
- **`M`'s own imports** — every name `M`'s file imports is in scope under the same binding it
  has in the file body. [S102]

**Parity is install-path-independent (MUST).** The environment MUST match `M`'s file-body
environment **regardless of how `M` was installed this session** — whether `M` was freshly
typechecked, or **restored from the module cache**. A cache-restored module MUST NOT present a
degraded namespace turn (e.g. a restored module whose session environment lacks the prelude, so
`(+ x 1)` fails with `undefined variable: +`). This is the parity axis: fresh and
cache-restored `/mod M` turns are indistinguishable to the user. [S102]

| Requirement | Test |
|---|---|
| a `/mod M` turn using prelude operators compiles (fresh session) | [Tested tests/repl_mod_devloop.rs::devloop_fresh_prelude_using_mod_turn_compiles] |
| the SAME turn compiles identically in a cache-restored session (parity axis) | [Tested tests/repl_mod_devloop.rs::devloop_cache_restored_prelude_using_mod_turn_compiles] |
| a bare `:Int` type alias resolves in a `/mod M` defining turn | [Tested tests/repl_mod_devloop.rs::devloop_fresh_mod_turn_bare_type_alias_resolves] |
| the full file-backed dev loop (break → revert heal; cross-module + restart) works over `/mod M` turns | [Tested tests/repl_mod_devloop.rs::devloop_fresh_same_module_dependent_break_true_and_revert_heal, tests/repl_mod_devloop.rs::devloop_fresh_cross_module_revert_then_restart_runs_clean] |

### 3.10 Module-Qualified Arguments to Introspection Commands [S102]

The introspection commands' argument grammar MUST accept a **module-qualified name**
(`module/symbol`, spec `08-modules.md` §8.5.1) wherever they accept a bare symbol name. This is
a self-documentation requirement, not a convenience: the REPL's **own reports print
module-qualified names** — the §18.3 cascade report, `/list`, `/imports`, and `/refs` all
render dependents and callers as `m/mf` — and a name the REPL prints MUST be pasteable back
into the command that reads it. A qualified name that the REPL emits but its own introspection
commands reject is a broken self-documentation loop.

- **`/sig`, `/info`, `/doc`, `/source`, `/refs`, `/tests-for` MUST resolve a module-qualified
  argument** to the same symbol the bare form resolves to (when in scope), producing the same
  output. `/sig m/mf` MUST NOT report `unknown symbol 'm/mf'` while bare `mf` is imported and
  `m` is loaded. [S102]
- **`/sig` (and `/info`) on an imported bare name MUST print the full §3.8 primary line** — the
  `:(Fn …) m/mf ; defn - {doc}` signature line — not merely a `; imported from m/mf`
  provenance note with no signature. An imported name is as introspectable as a locally-defined
  one. [S102]
- **The names a cascade/`broken:` report prints MUST be pasteable into `/info`** to read the
  break details (the §18.3 ↔ §3.6 round trip). [S102]

| Requirement | Test |
|---|---|
| `/sig` accepts a module-qualified name | [Tested tests/repl_mod_devloop.rs::sig_accepts_fq_module_qualified_name] |
| `/info` accepts a module-qualified name | [Tested tests/repl_mod_devloop.rs::info_accepts_fq_module_qualified_name] |
| `/refs` accepts a module-qualified name (bare form is the control) | [Tested tests/repl_mod_devloop.rs::refs_accepts_fq_module_qualified_name, tests/repl_mod_devloop.rs::refs_bare_name_lists_cross_module_caller_control] |
| `/sig` on an imported bare name prints the full §3.8 primary line | [Tested tests/repl_mod_devloop.rs::sig_imported_name_shows_full_signature_line] |
| a cascade `broken:` name is pasteable into `/info` | [Tested tests/repl_mod_devloop.rs::cascade_report_broken_name_pasteable_into_info] |

## 4. Self-Documentation Contract

Every valid language construct entered at the REPL MUST produce useful feedback. This is the **self-documentation principle** from the project's design principles. All output reinforces the language syntax.

### 4.1 Symbol Lookup — Per-Class Specification

Entering a bare symbol name at the REPL MUST produce output following the universal format (§1.1). Every symbol class has a defined response. No valid name MUST produce an opaque error. If a name is unbound, the error MUST say so clearly. [Tested tests/repl_negative::unbound_symbol_clear_error]

#### 4.1.1 Functions (defn) [Tested tests/repl_introspection::bare_fn_lookup_after_defn_shows_defn_classification]

Primary line only. Classification `defn`. Docstring appended if present.

```
user> double
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2

user> id
:(Fn [a] a) user/id ; defn
```

Constrained functions show inline constraints per §1.4:

```
user> add
:(Fn [:Num a :a] a) user/add ; defn - Add two numbers
```

Overloaded functions show all variant signatures, one per line:

```
user> map
:(Fn [(Fn [a] b) (user/Vec a)] (user/Vec b)) user/map ; defn - Transform elements
:(Fn [(Fn [a] b) (user/List a)] (user/List b)) user/map
```

| Requirement | Test |
|---|---|
| function shows type + name | [Tested tests/repl_introspection::bare_fn_lookup_after_defn_shows_defn_classification] |
| constrained fn shows constraints | [Tested tests/repl_introspection::bare_fn_lookup_after_defn_shows_defn_classification] |
| overloaded fn shows all variants | [Tested tests/repl_introspection::display_overloaded_fn_shows_all_variants] |

#### 4.1.2 Constructors [Tested tests/repl_introspection::nullary_constructor_bare_lookup_dot_notation]

Primary line only. Classification `deftype` (constructors are created by `deftype`). Nullary constructors have no function type — just the ADT type.

```
user> Some
:(Fn [a] (user/Option a)) user/Option.Some ; deftype

user> Red
:user/Color user/Color.Red ; deftype
```

For single-constructor types where the constructor name matches the type name, the `Type.` prefix is suppressed:

```
user> Point
:(Fn [primitives/Int primitives/Int] user/Point) user/Point ; deftype
```

#### 4.1.3 Types (deftype) [Tested tests/repl_introspection::bare_type_lookup_includes_match_section]

Primary line plus related symbols. Classification `deftype` for user types, `type` for builtin types. Related symbols show constructors under `match:` (the language construct used with them) and trait implementations under `impl:`.

```
user> Color
:user/Color ; deftype
; match:
;  Red Green Blue

user> Option
:user/Option ; deftype
; match:
;  None Some
; impl:
;  Display Eq

user> Int
:primitives/Int ; type
; impl:
;  Display Eq Num Ord
```

Constructor names under `match:` are unqualified bare names. Trait names under `impl:` are unqualified. Within `impl:`, locally-defined traits appear first, then imported traits.

| Requirement | Test |
|---|---|
| builtin types (Int, Bool, Float, String) | [Tested tests/repl_introspection::bare_type_lookup_includes_match_section] |
| user-defined type | [Tested tests/repl_introspection::bare_type_lookup_includes_match_section] |
| related constructors | [Tested tests/repl_introspection::bare_type_lookup_includes_match_section] |
| related trait impls | [Tested+Neg tests/repl_introspection::bare_type_lookup_includes_match_section] |

#### 4.1.4 Traits (deftrait) [Tested tests/repl_introspection::bare_trait_lookup_includes_defn_section]

Primary line plus related symbols. Classification `deftrait`. Related symbols show method names under `defn:` and implementing types under `impl:`.

```
user> Display
:core.str/Display ; deftrait - Format as string
; defn:
;  show
; impl:
;  Point
;  Bool Float Int List Vec

user> Num
:core.numerics/Num ; deftrait - Numeric operations
; defn:
;  + - * /
; impl:
;  Float Int
```

Within `impl:`, locally-defined types appear first, then imported types. Method names under `defn:` are unqualified.

#### 4.1.5 Special Forms [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting]

Primary line only. Classification `special form`. Special forms display a function-like type signature that teaches their syntax shape.

```
user> if
:(Fn [primitives/Bool a a] a) if ; special form - Conditional branch

user> let
:(Fn [bindings body] a) let ; special form - Local bindings

user> defn
:(Fn [name params body] function) defn ; special form - Define function

user> defmacro
:(Fn [name docstring? params body] macro) defmacro ; special form - Define macro
```

| Form | Test |
|---|---|
| `if` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `let` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `fn` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `defn` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `deftype` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `match` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `defmacro` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |

#### 4.1.6 Macros (defmacro) [Tested]

Primary line plus clause signatures. Classification `defmacro`. Each clause shows its parameter list on a separate comment line.

```
user> twice
:user/twice ; defmacro - Evaluate and double
; [x] -> Sexp

user> my-add
:user/my-add ; defmacro - Variadic addition
; [x] -> Sexp
; [x y] -> Sexp
; [x y z] -> Sexp
```

Zero-arg macros expand immediately — they do not reach the lookup path.

| Requirement | Test |
|---|---|
| macro shows clause signatures | [Tested tests/repl_introspection::defmacro_display_single_clause] |
| multi-clause macro | [Tested tests/repl_introspection::defmacro_display_single_clause] |

#### 4.1.7 Primitive Functions [Tested+Neg tests/repl_introspection::bare_primitive_add_i64_at_prompt_displays_type_and_fqn, tests/repl_introspection::bare_primitive_lookup_not_empty_neg]

Primary line only. Classification `primitive` (distinguishes builtins from user-defined `defn`). Primitives are defined in the `primitives` module.

```
user> add-i64
:(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64 ; primitive - Add

user> str-concat
:(Fn [primitives/String primitives/String] primitives/String) primitives/str-concat ; primitive - Concatenate two strings
```

The classification word `primitive` (rather than `defn`) is intentional: it distinguishes host-implemented builtins from user-defined functions. The builtin's docstring (sourced from [Appendix A.5](../spec/appendix-a-builtins.md#a5-docstrings-for-builtins-r1)) follows the classification in the same `; {classification} - {docstring}` dash form per §1.1.


#### 4.1.8 Trait Methods (including operators) [Tested tests/repl_introspection::operator_plus_bare_lookup_displays_signature]

Trait methods use `Trait.method` dot notation in the name position, fully qualified with the defining module. Classification `deftrait` (methods are declared by `deftrait`).

```
user> +
:(Fn [:core.num/Num a :a] a) core.num/Num.+ ; deftrait - Addition operator

user> show
:(Fn [:core.str/Display a] primitives/String) core.str/Display.show ; deftrait - Format as string

user> =
:(Fn [:core.cmp/Eq a :a] primitives/Bool) core.cmp/Eq.= ; deftrait
```

This applies to all trait methods, not just operators. The `Trait.method` notation is valid input syntax (per spec §1.4.4), reinforcing discoverability.

#### 4.1.9 Modules [R4]

Primary line plus related symbols. Classification `mod`. Related symbols show the module's public exports under `exports:`.

```
user> math
:math ; mod
; exports:
;  foo bar
```

Module lookup is Ring 4 scope.

#### 4.1.10 Unbound Names [Tested tests/repl_negative::unbound_symbol_clear_error]

An unbound name MUST produce a clear error message, not an opaque internal error. The session MUST continue.

```
user> xyz
error: unbound symbol 'xyz'
```

## 5. Error Presentation [Tested]

### 5.1 Error Format [Tested]

All errors MUST display:

1. The error category (parse error, type error, etc.) [Tested tests/repl_negative::type_error_arg_mismatch]
2. The source location (file/line/column or character span) [Tested tests/repl_negative::type_error_arg_mismatch]
3. A human-readable message [Tested tests/repl_negative::type_error_arg_mismatch]

Errors MUST be written to stdout (as part of the REPL conversation flow, visible in piped output and the showcase). Stderr is reserved for traces and diagnostic output. Errors MUST NOT crash the REPL session — the user MUST be able to continue entering expressions after any error. [Tested+Neg tests/repl_negative::type_error_arg_mismatch, tests/repl_negative::type_error_neg_stderr_empty_and_session_survives]

### 5.2 Error Recovery [Tested]

After any error (parse, type, runtime), the REPL MUST:
- Display the error [Tested tests/repl_introspection::sig_unknown_name_graceful]
- Reset input state (clear any partial multi-line input)
- Present the prompt for new input

The session state (defined functions, types, modules) MUST NOT be corrupted by an error in a subsequent expression. [Tested+Neg tests/repl_introspection::sig_unknown_name_graceful]

### 5.3 Type Error Quality [Tested]

Type errors MUST include:
- The expected type (fully qualified) [Tested tests/repl_negative::type_error_names_expected_type_fully_qualified]
- The actual (inferred) type (fully qualified) [Tested tests/repl_negative::type_error_arg_mismatch] [Tested tests/repl_negative::type_error_names_actual_type_fully_qualified]
- The source location of the mismatch [Tested tests/repl_negative::type_error_has_source_location]

Type errors SHOULD suggest common fixes when applicable.

## 6. Discoverability [Tested]

### 6.1 First Five Minutes [Tested tests/repl_lifecycle::first_session_journey_launch_to_confidence]

A new user opening the REPL with no prior knowledge MUST be able to:

1. See that `/help` is available (mentioned in the startup banner or prompt)
2. Evaluate a simple expression and see a typed result: `(+ 1 2)` → `:primitives/Int 3`
3. Define a function and see its inferred type: `(defn id [x] x)` → `:(Fn [a] a) user/id`
4. Find available operators and functions via `/list`
5. Get help on any symbol via `/info` or `/sig`

### 6.2 Startup Banner [Tested tests/repl_lifecycle::boot_shows_banner]

The REPL MUST display a startup banner including:
- The language name and version
- A hint about `/help`

The banner SHOULD be concise (3 lines or fewer).

### 6.3 First Session Journey [Tested tests/repl_lifecycle::first_session_journey_launch_to_confidence]

The "first five minutes" (§6.1) lists capabilities. This section scripts the **narrative arc** — the sequence a new user follows from launch to confidence. Each step builds on the previous one; nothing requires prior knowledge. This journey defines the `first-session.demo` showcase script.

**Phase 1: Orientation** (banner → `/help`)

The user launches cranelisp and sees a banner with the language name and a `/help` hint. They type `/help`. The output shows them slash commands exist, organized by purpose. They now know there is a self-documentation system. *(Ring 0)*

**Phase 2: First evaluation** (expression → typed result)

The user types a simple expression. The result shows `:Type value` format — they learn that the REPL always shows types. They try a few more: booleans, arithmetic. Each result reinforces the `:Type value` pattern. *(Ring 0)*

**Phase 3: Defining things** (defn → type inference)

The user defines a function. The REPL shows the inferred type scheme and qualified name. They call it. They see that the REPL inferred the types without annotation. *(Ring 0)*

**Phase 4: Introspection** (`/sig`, `/list`, `/info`)

The user wants to see what they've defined. `/list` shows their definitions. `/imports` shows what's available from elsewhere (including special forms). `/sig` shows a function's type. `/info` shows full details. They discover that the REPL knows about everything and can explain it. *(Ring 0)*

**Phase 5: Making mistakes** (error → recovery)

The user makes a type error. The error message names the expected and actual types. They continue typing — the session is intact. They learn the REPL is resilient. *(Ring 0)*

**Phase 6: Self-documentation** (bare symbols, special forms)

The user types a function name bare. The REPL shows its type. They type `if` bare. It shows the special form's shape. They learn that any name typed bare produces documentation, not an error. *(Ring 0)*

**Phase 7: Richer types** (strings, ADTs, Vecs)

The user creates a string, defines an ADT, pattern-matches on it. They create a Vec. Each value displays in a readable format that mirrors the language syntax. *(Ring 1)*

**Phase 8: Composition** (closures, higher-order, putting it together)

The user combines what they've learned: a closure over an ADT, applied via a higher-order function, stored in a Vec. The REPL handles it all. They feel confident. *(Ring 1)*

Later rings extend this journey with modules (`/mod`), traits, macros (`/expand`), and IO, but the core loop — evaluate, inspect, make mistakes, recover — is established by Ring 1.

### 6.4 Tab Completion [R4 S11]

The REPL SHOULD support tab completion for:
- Symbol names (functions, types, constructors)
- Slash commands
- Module names (after `/mod`)

This is a SHOULD, not a MUST, because it depends on the terminal library.

## 7. Performance Targets

### 7.1 Startup Time [Tested tests/build_confidence::perf_simple_eval_latency_under_2000ms]

The REPL MUST start and display a prompt within **500ms** on a modern machine (defined as: Apple M-series or equivalent x86-64, SSD, 8GB+ RAM). This includes loading the prelude.

### 7.2 Expression Evaluation [Tested tests/build_confidence::perf_simple_eval_latency_under_2000ms]

Simple expressions (arithmetic, boolean logic, small function calls) MUST evaluate and display within **50ms** of the user pressing Enter. This is the combined compile + eval time. This budget holds regardless of background compilation: the scheduler's priority ladder ranks blocking REPL/typecheck work above non-blocking JIT codegen, so an in-flight prelude or module compile does not starve a trivial REPL submission. The tested latency bound (`tests/build_confidence.rs::perf_simple_eval_latency_under_2000ms`) is the normative guard; a dedicated REPL-priority work level is not required unless a regression pushes trivial-form latency past this budget under worker contention.

### 7.3 Prompt Responsiveness [R4 S10]

After displaying a result, the next prompt MUST appear within **10ms**. There MUST be no perceptible delay between result display and prompt readiness.

### 7.4 Large Output [Tested tests/build_confidence::repl_large_vec_output_bounded_under_64kb]

When displaying large values (e.g., a Vec with 1000 elements), the REPL SHOULD truncate output with an indication of the total size rather than flooding the terminal. The truncation threshold is implementation-defined but SHOULD be configurable.

## 8. Ring 2B Module Demo Scenarios [R4 S10]

When the module system is fully wired (Ring 2B), these 7 REPL scenarios validate the module experience. Each scenario has a concrete expected behavior.

**Scenario 1: `/mod math` switches namespace**
```
user> /mod math
math>
```
The prompt changes to reflect the active module. Definitions entered now belong to `math`. The `/mod` command MUST NOT print a confirmation message — the prompt change is sufficient feedback.

**Scenario 2: `/mod user` switches back**
```
math> /mod user
user>
```
Switching back to `user` restores the default namespace. Previously defined `math` symbols remain accessible via qualified names.

**Scenario 3: `(import [math [foo]])` loads module**
```
user> (import [math [foo]])
```
After defining `foo` in the `math` module (via `/mod math` + `defn`), importing it makes `foo` available as a bare name in `user`.

**Scenario 4: Qualified access `math/foo`**
```
user> math/foo
:(Fn [primitives/Int] primitives/Int) math/foo
```
Without importing, any symbol can be accessed via its qualified path.

**Scenario 5: `/list` shows only definitions**
```
math> /list
Fns:
  foo
```
The `/list` command shows only that module's own definitions — not imports, not special forms. Names are unqualified (they belong to the current module). After switching back to `user` with no definitions:
```
user> /list
(no definitions)
```
`/list` is empty because the user hasn't defined anything yet. Imports and special forms are on `/imports`.

**Scenario 5b: `/imports` shows imports and special forms**
```
user> (import [math [foo]])
user> /imports
Special forms:
  defn deftype fn if let match
Fns:
  foo
```
Special forms always appear in `/imports` (they're available but not user-defined). The imported `foo` appears under Fns. For detail on where imports came from:
```
user> /imports math
From math:
  foo
```
The source module filter groups names by source. Type `foo` for its type signature.

**Scenario 6: `/mod` with no argument resets to `user`**
```
math> /mod
user>
```
Bare `/mod` with no argument switches back to the `user` module. The current module is always visible in the prompt, so a "show current" command is redundant. `/mod` is the quickest way home.

**Scenario 7: Unknown module gives clear error**
```
user> /mod nonexistent
Error: Module 'nonexistent' not found. Use /mod <name> to create a new module.
```
The error message is actionable — it tells the user what to do next.

## 10. Terminal Styling [R4 S22]

When connected to a colour-capable terminal, the REPL MUST apply ANSI styling to distinguish output categories. Styling makes the `:Type value` format scannable — the type prefix, the value, and the classification comment are visually distinct without requiring the user to parse punctuation.

### 10.1 TTY Detection and Suppression [R4 S22]

Colour MUST be enabled by default on capable terminals and suppressed otherwise. The detection logic, in priority order:

1. **`--no-color` flag**: If the `--no-color` CLI flag is present, all ANSI output MUST be suppressed. This flag MUST be accepted alongside other flags (e.g., `cranelisp --no-color`, `cranelisp --run file.cl --no-color`).
2. **`NO_COLOR` environment variable**: If `NO_COLOR` is set to any non-empty value, all ANSI output MUST be suppressed (per https://no-color.org). The value is irrelevant — `NO_COLOR=1`, `NO_COLOR=true`, and `NO_COLOR=` (empty) all suppress except the empty string case: `NO_COLOR=` (set but empty) does NOT suppress.
3. **TTY check**: If stdout is not a terminal (`!isatty(stdout)`), all ANSI output MUST be suppressed. This covers piped output (`cranelisp | less`), redirected output (`cranelisp > log.txt`), and batch mode (`--run`).
4. **Otherwise**: Colour is enabled.

There is no `--color=force` flag. If a user needs colour in piped output (e.g., for `less -R`), they can use a tool like `unbuffer` or `script`. Keeping the implementation simple is more important than covering this edge case.

### 10.2 SGR Escape Convention [R4 S22]

All styling uses ANSI SGR (Select Graphic Rendition) sequences only — no cursor movement, no alternate screen, no 256-colour or truecolor. The palette is restricted to the base 8 colours (30-37) plus bright variants (90-97) and attributes bold (1) and dim (2). This ensures legibility across all terminal emulators, including the macOS default Terminal.app which has limited truecolor support.

Every styled span MUST be terminated by a reset (`\033[0m`) before any newline or before transitioning to a differently-styled span. Unterminated escape sequences corrupt subsequent output and are a conformance failure.

Escape sequences MUST NOT appear inside the value portion of `:Type value` when that value is a String literal — the string content is user data and MUST be printed verbatim.

### 10.3 Colour Palette [R4 S22]

The palette assigns one colour per semantic role. There are no user-configurable themes — the defaults are chosen to work on both light and dark terminal backgrounds using the standard 16-colour ANSI palette.

| Element | Style | SGR Code | Reset | Rationale |
|---|---|---|---|---|
| Prompt (timing + module + `>`) | dim | `\033[2m` | `\033[0m` | Recedes from focus; always visible but never competing |
| Result type (`:Type` prefix) | cyan | `\033[36m` | `\033[0m` | Distinct from value; teaches the type system visually |
| Result value | default | — | — | Primary content; no styling needed |
| Classification comment (`; defn`, `; deftrait`, etc.) | dim | `\033[2m` | `\033[0m` | Metadata — present but subordinate to the type+value |
| Related-symbol comment lines (`; defn:`, `; impl:`, names) | dim | `\033[2m` | `\033[0m` | Secondary information following the primary line |
| Error keyword (`Error:`) | bold red | `\033[1;31m` | `\033[0m` | Immediately noticeable |
| Error detail (message body) | red | `\033[31m` | `\033[0m` | Contextually connected to the error keyword |
| Warning keyword (`Warning:`) | bold yellow | `\033[1;33m` | `\033[0m` | Less urgent than errors, still attention-getting |
| Warning detail | yellow | `\033[33m` | `\033[0m` | Contextually connected to the warning |
| Slash command category headers (`Fns:`, `Types:`, etc.) | bold | `\033[1m` | `\033[0m` | Anchors for scanning `/list`, `/imports`, `/exports` |
| Slash command body (symbol names, info lines) | default | — | — | Dense informational content; styling would add noise |
| Startup banner | dim | `\033[2m` | `\033[0m` | One-time context; should not dominate |
| Agent prose frame (`▌` gutter + agent text) | bright magenta gutter, default body | `\033[95m` (gutter) | `\033[0m` | Reserved exclusively for the agent's *prose* — makes model output unmistakable from deterministic REPL output (§17.2). Only the prose is framed; agent-issued commands and their results use their normal roles. [S88] |
| Agent-input prompt (`agent>` glyph at agent-echo sites) | dim, bright-magenta `agent` token | `\033[2m` + `\033[95m` (the `agent` token) | `\033[0m` | The prompt prefix shown when the agent "types" a line — a pulled read command (§17.2) or a Build-submit echo (§17.14). Distinct from the dim human prompt (§2.1) and from the `▌` prose gutter, so the transcript reads honestly: who issued each line. Degrades under `--no-color`/non-TTY to the plain-text token `agent>` (no SGR). [S89] |

Notes on specific choices:

- **No green for comments.** The earlier draft used green for `;` comment lines. However, REPL output comment lines (`;`) carry structured information (classifications, related symbols) — they are not "comments" in the source-code sense. Dim is more appropriate: it creates a visual hierarchy (type = cyan, value = default, metadata = dim) without introducing a third saturated colour.
- **Bold for category headers only.** Bold is reserved for structural anchors (category names in `/list` output, error/warning keywords). Using bold elsewhere dilutes its signal.
- **No colour on user input.** The line editor controls input styling. The REPL MUST NOT emit escape sequences into the input buffer.

### 10.4 Styled Universal Output Format [R4 S22]

The universal output format (§1.1) with styling applied. Angle brackets show styled spans; actual output uses SGR codes, not brackets.

**Expression result:**
```
<cyan>:primitives/Int</cyan> 42
```

**Definition with classification and docstring:**
```
<cyan>:(Fn [primitives/Int] primitives/Int)</cyan> user/double <dim>; defn - Multiply by 2</dim>
```

**Type with related symbols:**
```
<cyan>:user/Color</cyan> <dim>; deftype</dim>
<dim>; match:</dim>
<dim>;  Red Green Blue</dim>
```

**Error:**
```
<bold-red>Error:</bold-red> <red>Unbound symbol 'foo'</red>
```

**Slash command `/list`:**
```
<bold>Types:</bold>
  Color Point
<bold>Fns:</bold>
  double area
```

The reset between the cyan type prefix and the default-styled value is the space character — no visible break, just a colour transition. The classification comment (everything from `; ` onward on the primary line) is a single dim span.

### 10.5 Batch Mode Output [R4 S22]

Batch mode (`--run`) writes to stdout which is typically not a TTY. Per §10.1, ANSI sequences MUST be suppressed. The `:Type value` format is emitted as plain text. Error messages to stderr MUST also be plain text in batch mode (stderr TTY status is checked independently — if stderr is a TTY but stdout is not, errors MAY be styled on stderr).

### 10.6 Showcase Player Styling [R4 S22]

The showcase player (`repl/showcase`) MAY apply the same colour palette during replay. Specifically:

- Prompt lines SHOULD use dim styling, matching the REPL prompt.
- Simulated user input SHOULD use default (no styling) — matching the visual weight of real typing.
- Output lines SHOULD be styled using the same rules as §10.3 (cyan for types, dim for comments, red for errors).
- The `[paused]` indicator SHOULD use dim styling.
- The showcase player MUST respect `NO_COLOR` and TTY detection using the same logic as the REPL (§10.1), minus the `--no-color` flag (the player has its own invocation interface).

### 10.7 Implementation Notes [R4 S22]

The styling layer SHOULD be implemented as a small module (e.g., `src/style.rs`) that provides a `Style` enum and a `styled(text, style) -> String` function. When colour is disabled, `styled` returns the text unchanged. All REPL output code calls `styled` — there are no raw `\033[` literals scattered through the codebase.

The TTY detection result SHOULD be computed once at startup and stored as a boolean. Checking `isatty()` on every line would be wasteful and could produce inconsistent output if stdout is redirected mid-session (which is not a supported scenario but should not cause crashes).

**Ring 4 Sprint 22**: Full terminal styling specification. Implementation targeted for a subsequent sprint.

## 9. Ring Testability Matrix

| Requirement | Ring 0 | Ring 1 | Ring 2 | Ring 3 | Ring 4 |
|---|---|---|---|---|---|
| `:Type value` display | Int, Bool, Float, enum ADT | + String, data ADT, Vec, List, closures | + Seq | | + IO |
| Definition display | function type + qualified name | | + constrained, overloaded | + macro | |
| Prompt with timing | yes | | + module name | | |
| `/help` | yes | | | | |
| `/sig`, `/doc`, `/type`, `/info` | yes | | | | |
| `/source`, `/sexp`, `/ast`, `/clif`, `/disasm` | yes | | | | |
| `/list` | Types, Fns | | + Traits, Modules | + Macros | |
| `/time` | yes | | | | |
| `/expand` | | | | yes | |
| `/mod` | | | yes | | |
| Demo trampoline | | | | | yes |
| `/mem` | | yes | | | |
| `/run-tests`, `/run-all-tests` | | | | | yes |
| Shell escape (`/sh`) | | | | | yes |
| File watching | | | | | yes |
| Self-documentation | bare symbol, special forms, operators (qualified) | | + traits, modules | + macros | |
| Error recovery | yes | | | | |
| Startup < 500ms | yes | | | | |
| Eval < 50ms (simple) | yes | | | | |
| Fully-qualified names | all output | | | | |
| `Type.Constructor` notation | yes | | | | |

## 11. Ring 3 REPL Requirements [Tested tests/repl_introspection::expand_user_defmacro]

Ring 3 introduces the macro system. The REPL MUST integrate macros into all existing introspection and display mechanisms so that macros are first-class citizens of the self-documentation experience.

### 11.1 `/expand` Command [Tested+Neg tests/repl_introspection::expand_user_defmacro]

The `/expand` (alias `/e`) command MUST accept a single S-expression form, perform recursive macro expansion to a fixed point (per spec Section 9.3.3), and display the fully expanded S-expression WITHOUT evaluating it.

```
user> /expand (double-list 1 2)
(Cons 1 (Cons 1 (Cons 2 (Cons 2 Nil))))
user> /expand (cond (> x 0) "pos" (= x 0) "zero" "neg")
(if (> x 0) "pos" (if (= x 0) "zero" "neg"))
user> /expand (+ 1 2)
(+ 1 2)
```

If the input form contains no macro calls, `/expand` MUST display it unchanged. If expansion fails (e.g., arity mismatch, expansion limit exceeded), `/expand` MUST display the error without corrupting session state.

The output MUST be a valid S-expression string. Fully-qualified constructor names generated by quasiquote expansion (e.g., `macros/SexpSym`) SHOULD be simplified to bare names when they are unambiguous in context.

### 11.2 Macro Introspection [Tested tests/repl_introspection::list_shows_macros_after_defmacro]

Macros MUST appear in existing REPL introspection commands alongside functions and types.

#### 11.2.1 `/list` — Macros Category [Tested+Neg tests/repl_introspection::list_shows_macros_after_defmacro]

`/list` MUST include a "Macros" category listing all macros defined in the current module (per §3.3). Macros MUST be listed by their unqualified name.

```
user> /list
Macros:
  double-list when
Fns:
  ...
```

#### 11.2.2 `/info` — Macro Details [Tested tests/repl_introspection::doc_macro_with_docstring] [Tested tests/repl_introspection::info_multi_clause_macro_shows_clause_count]

`/info <name>` for a macro MUST display the universal format (§1.1) with classification `defmacro`, clause signatures, and docstring.

```
user> /info cond
:user/cond ; defmacro - Multi-way conditional with mandatory default
; [x] -> Sexp
; [x body & rest] -> Sexp
  2 clauses
user> /info when
:user/when ; defmacro
; [cond body] -> Sexp
```

#### 11.2.3 `/sig` — Macro Signature [Tested tests/repl_introspection::bare_macro_lookup_shows_clause_signature]

`/sig <name>` for a macro MUST display the clause signatures using the universal format (§1.1, §4.1.6), with `& rest` syntax for variadic parameters and bracket notation for bracket destructuring.

```
user> /sig cond
:user/cond ; defmacro
; [x] -> Sexp
; [x body & rest] -> Sexp

user> /sig bind!
:prelude/bind! ; defmacro
; [[name expr & bindings] body] -> Sexp

user> /sig when
:user/when ; defmacro
; [cond body] -> Sexp
```

#### 11.2.4 `/doc` — Macro Docstring [Tested tests/repl_introspection::doc_macro_no_docstring]

`/doc <name>` for a macro MUST display the macro's docstring. If the macro has no docstring, `/doc` MUST display a message indicating none is available.

```
user> /doc list
:prelude/list ; defmacro - Construct a list from elements

user> /doc my-macro
:user/my-macro ; defmacro
  no docstring
```

### 11.3 `defmacro` Display [Tested tests/repl_introspection::defmacro_display_single_clause, tests/repl_introspection::defmacro_display_multi_clause]

When the user defines a macro at the REPL, the display MUST confirm the definition using the universal format (§1.1, §4.1.6):

```
user> (defmacro double [x] `(+ ~x ~x))
:user/double ; defmacro
; [x] -> Sexp

user> (defmacro cond ([x] x) ([x body & rest] `(if ~x ~body (cond ~@rest))))
:user/cond ; defmacro
; [x] -> Sexp
; [x body & rest] -> Sexp
```

This mirrors the definition display pattern established for functions (Section 1.3) and types, keeping the REPL output self-documenting.

### 11.4 Bare Macro Lookup [Tested tests/repl_introspection::bare_macro_lookup, tests/repl_introspection::bare_macro_lookup_shows_clause_signature]

Entering a macro name as a bare symbol (without arguments) MUST produce output per the universal format (§1.1, §4.1.6). Zero-argument macros are an exception: they expand immediately via bare-symbol expansion (spec Section 9.5) rather than displaying introspection.

```
user> double
:user/double ; defmacro
; [x] -> Sexp

user> cond
:prelude/cond ; defmacro
; [x] -> Sexp
; [x body & rest] -> Sexp
```

### 11.5 Sprint 11 Test Scenarios [R3 S11]

The following test scenarios validate the Ring 3 REPL macro experience. Each MUST have a corresponding test in `tests/`.

| # | Scenario | Expected Behavior | Spec Reference | Test |
|---|---|---|---|---|
| 1 | `/expand` with a single macro | Displays expanded form without evaluation | §11.1, §9.3.2 | [Tested tests/repl_introspection::expand_user_defmacro] |
| 2 | `/expand` with nested macros | Displays fully expanded form (recursive to fixed point) | §11.1, §9.3.3 | [Tested tests/repl_introspection::expand_recursively_to_fixpoint] |
| 3 | `/expand` with no macro calls | Displays input unchanged | §11.1 | [Tested+Neg tests/repl_introspection::expand_neg_non_macro_unchanged] |
| 4 | `/list` after `defmacro` | Macro appears under "Macros" category | §11.2.1, §3.3 | [Tested tests/repl_introspection::list_shows_macros_after_defmacro] |
| 5 | `/info` on a multi-clause macro | Shows universal format with clause signatures and docstring | §11.2.2 | [Tested tests/repl_introspection::info_multi_clause_macro_shows_clause_count] |
| 6 | `/sig` on a variadic macro | Shows universal format with `& rest` clause signature | §11.2.3 | [Tested tests/repl_introspection::bare_macro_lookup_shows_clause_signature] |
| 7 | `defmacro` display at REPL | Shows universal format `:module/name ; defmacro` with clause signatures | §11.3, §9.13 | [Tested tests/repl_introspection::defmacro_display_single_clause] |
| 8 | Bare macro name lookup | Shows universal format with clause signatures (non-zero-arg macros) | §11.4, §4.1.6 | [Tested tests/repl_introspection::bare_macro_lookup] |

## 12. Demo Trampoline [R4 S23]

The demo player (§10.6) SHOULD support `/quit` within a demo script by restarting the REPL process and continuing with the remaining script lines. This allows demo scripts to demonstrate session restart naturally:

```
; Define something
(defn foo [] 42)
(foo)
; Restart and show it's gone
/quit
; New session starts here
foo
; error: undefined symbol 'foo'
```

When the demo player detects that the REPL process has exited (due to `/quit` or EOF), it SHOULD start a new REPL process and pipe the remaining demo lines into it. The demo ends when the script is exhausted, not when the first REPL exits.

## 13. Shell Escape [R4 S52]

The REPL supports a `/sh` slash command for running operating system commands without leaving the REPL session. This is useful for checking file contents, running external tools, or verifying output during iterative development.

### 13.1 Syntax [R4 S52]

The shell escape command is `/sh <command>`:

```
user> /sh ls -la
```

`/sh` follows the same slash-command convention as all other REPL commands (§3). Everything after `/sh` and optional whitespace is the shell command string.

### 13.2 Execution [Tested tests/repl_shell::shell_escape_basic_echo_command_runs]

The command string (everything after `/sh` and optional whitespace) MUST be passed to the system shell for execution. On Unix-like systems, this means invoking `/bin/sh -c "<command>"`. The REPL MUST NOT attempt to parse or interpret the command itself.

The command runs synchronously — the REPL blocks until the command completes. The REPL prompt is not displayed until the command finishes.

### 13.3 Output Handling [Tested tests/repl_shell::shell_escape_quoted_args_pass_through_to_stdout]

The command's stdout and stderr MUST be passed through directly to the terminal. The REPL does NOT capture, buffer, or reformat the output. The user sees exactly what the command produces, interleaved as the OS delivers it.

```
user> /sh echo "hello from shell"
hello from shell
0+0ms; user>
```

### 13.4 Exit Code Display [Tested+Neg tests/repl_shell::shell_escape_nonzero_exit_code_is_displayed]

If the command exits with a non-zero status, the REPL MUST display the exit code after the command output:

```
user> /sh false
exit status: 1
0+0ms; user>
```

If the command exits with status 0, no exit code is displayed — silence means success.

If the command is terminated by a signal (e.g., SIGKILL), the REPL SHOULD display the signal information:

```
user> /sh kill -9 $$
killed by signal: 9
0+0ms; user>
```

### 13.5 No REPL State Interaction [Tested+Neg tests/repl_shell::shell_escape_does_not_disturb_repl_state]

Shell escape is a pure passthrough. The command MUST NOT affect REPL state in any way:
- No variables, definitions, or imports are modified.
- The current module is unchanged.
- The typechecker, code cache, and compilation state are untouched.
- Environment variables set by the command do NOT propagate back to the REPL process (the command runs in a child process).

### 13.6 Edge Cases [Tested+Neg tests/repl_shell::shell_escape_neg_empty_command_does_not_error_or_crash]

**No arguments:** `/sh` with no command (or only whitespace) MUST print a usage hint: `Usage: /sh <command>`. [R4 S52]

```
user> /sh
Usage: /sh <command>
0+0ms; user>
```

**Command not found:** If the shell cannot find the command, the shell's own error message is passed through (since stdout/stderr are not captured). The exit code is displayed per §13.4.

```
user> /sh nonexistent-command
/bin/sh: nonexistent-command: command not found
exit status: 127
0+0ms; user>
```

**Multi-line:** Shell escape does NOT support continuation lines. Each `/sh` invocation is a self-contained command. For multi-statement commands, use shell syntax (e.g., `/sh echo a && echo b`).

**Timing:** The prompt after a shell escape MUST show `0+0ms` — shell commands are not Cranelisp evaluations and do not contribute to compile/eval timing.

### 13.7 `/help` Integration [Tested tests/repl_shell::shell_escape_listed_in_help_output]

`/sh` MUST appear in `/help` output as:

```
  /sh <cmd>       Run a shell command
```

## 14. File Watching [R4 S23]

The REPL automatically detects when source files change on disk, eagerly recompiles the affected modules, and notifies the user of the result. The developer edits files in their editor, saves, and the REPL immediately recompiles — no manual reload command needed.

### 14.1 Watch Scope [Tested tests/repl_watch::watch_emits_notification_when_loaded_module_source_changes]

The file watcher MUST monitor directories that contain source files actually loaded during the current session. This includes:
- The project root directory (if one was determined at startup).
- Directories of modules loaded via `(import ...)` or `/mod`, and their transitive dependencies.

The watcher SHOULD use OS-level filesystem notification (e.g., `FSEvents` on macOS, `inotify` on Linux) rather than polling. This provides near-instant detection without CPU overhead.

New files in watched directories SHOULD be detected, but they do not trigger any action until they are referenced by an import or module load.

The watcher MUST NOT watch directories that have not been imported. Stdlib directories are watched only if the prelude or a user module actually imported from them.

### 14.2 Eager Recompilation [Tested+Neg tests/repl_watch::watch_does_not_notify_on_metadata_only_change]

When a `.cl` source file is modified (content change, not just metadata/timestamp), the watcher MUST:

1. **Identify the module.** Map the changed file path to its module identity in the module graph.
2. **Clear old module state.** Remove the module's previous definitions from the typechecker, trait registry, and symbol tables so that recompilation does not conflict with existing definitions.
3. **Recompile immediately.** Re-read, re-parse, re-typecheck, and re-compile the module. Update GOT entries so callers get the new code.
4. **Cascade to dependents.** Dependents of the changed module MUST also be recompiled in topological order.
5. **Notify the user of the result.** Display `[updated: <file>]` on success or `[errors: <file>]` on failure (see §14.3).

Recompilation is **eager** — it happens as soon as the change is detected (at the next poll opportunity, before the next prompt), not deferred until the module is accessed.

Content hash comparison MUST be used to skip metadata-only changes (e.g., `touch foo.cl`). The watcher records the content hash of each source file when it is first loaded and compares against it on each filesystem event. Only true content changes trigger recompilation.

### 14.3 Notification Format [Tested tests/repl_watch::watch_notification_uses_bracketed_file_format]

The recompilation result IS the notification. There is no separate `[changed: ...]` message.

**On success:**

```
0+0ms; user> (+ 1 2)
:primitives/Int 3
[updated: math.cl]
0+0ms; user>
```

The format is `[updated: <file>]` where `<file>` is the path relative to the project root. If multiple modules were recompiled (including cascade dependents), each gets its own notification line.

**On failure:**

```
0+0ms; user> (+ 1 2)
:primitives/Int 3
[errors: math.cl]
  math.cl:5:3 — type error: expected Int, got String
0+0ms; user>
```

The format is `[errors: <file>]` followed by the error details on indented lines. The error details use the standard error format (§5.1).

**Input preservation (nice-to-have):** If the user is mid-input when a notification arrives, the notification SHOULD print on a new line, then reinstate the partial input line so typing is uninterrupted. Implementation MAY use rustyline's `ExternalPrinter` API for this. As an interim approach, notifications MAY be deferred until the next prompt boundary (before the prompt is printed). Notifications MUST NOT corrupt the user's input.

### 14.4 Error Blocking [Tested tests/repl_watch::watch_errors_block_evaluation_no_last_known_good]

When a module fails to recompile, the REPL MUST block further evaluation until the error is resolved:

1. The module is added to the session's error set.
2. Before evaluating any expression, the REPL checks the error set. If non-empty, it refuses evaluation with a message: `Cannot evaluate: module '<name>' has errors. Fix the source file and save.`
3. Slash commands (`/help`, `/quit`, etc.) remain available during error blocking — only expression evaluation is blocked.
4. When the source file is modified again (presumably with a fix), the watcher triggers another recompilation attempt. If recompilation succeeds, the module is removed from the error set, and evaluation resumes normally. If it fails again, the error set is updated with the new error.

There is **no last-known-good fallback**. Source code diverging from runtime behavior is dangerous — the user must see the error and fix it. The error blocking ensures they cannot accidentally evaluate code that depends on a broken module.

```
[errors: math.cl]
  math.cl:5:3 — type error: expected Int, got String
0+0ms; user> (+ 1 2)
Cannot evaluate: module 'math' has errors. Fix the source file and save.
0+0ms; user>
;; User fixes math.cl and saves...
[updated: math.cl]
0+0ms; user> (+ 1 2)
:primitives/Int 3
```

### 14.5 Module State on Error [R4 S23]

When a module fails to recompile:

1. The old module state has already been cleared (§14.2 step 2).
2. The module is in an error state — its definitions are unavailable.
3. The error set prevents evaluation from proceeding (§14.4).
4. The module remains watched. The next file modification triggers another recompilation attempt.

This "errors block" approach is preferable to "last-known-good" because it prevents the dangerous situation where the source file says one thing but the runtime does another. The user is forced to address the error before continuing.

### 14.6 Clearing Errors [R4 S23]

Error-locked modules (§14.4) are cleared when the offending file is fixed and saved — the watcher detects the change, recompiles successfully, and removes the module from the error set. The user can also restart the REPL (`/quit`) to clear all state.

### 14.7 Interaction with Object Cache [Tested tests/repl_watch::watch_change_triggers_cache_directory_creation]

File watching and the object cache work together:
- Recompilation invalidates and replaces cache entries for changed modules.
- Unchanged modules continue to use their cached `.o` files.
- Failed recompilations do NOT update the cache — the stale cache entry remains until a successful recompilation replaces it.

This means that after editing one file, only that file and its dependents are recompiled — unchanged modules load instantly from cache.

## 15. REPL Session Persistence [R4 S52]

### 15.1 Source Regeneration [Tested tests/repl_persist::persist_user_cl_is_created_with_definition_after_session]

The REPL MUST persist interactive definitions to disk by maintaining a backing `.cl` file for the entry module (e.g. `user.cl`). When the user enters a definition that compiles successfully:

1. The definition MUST be compiled and installed in the session. [R4 S52]
2. The entry module's backing `.cl` file MUST be **regenerated** atomically from the module's current state. The regeneration is performed by the REPL after eval — it is not part of the compilation or `.o` caching pipeline. [R4 S52]

The regenerated source file MUST be valid, parseable Cranelisp source — loading it through the normal module graph pipeline MUST reproduce the same session state. [R4 S52]

Definitions that fail to compile MUST NOT trigger regeneration — the backing file reflects only the last successfully compiled state. [R4 S52]

### 15.2 Session Restore [Tested tests/repl_persist::persist_defn_survives_restart_via_user_cl]

On REPL startup, the entry module's backing `.cl` file MUST be loaded through the normal module graph pipeline (with cache hit for fast restore). Definitions from the previous session MUST survive restart — the user resumes where they left off. [R4 S52]

If the backing file does not exist (first session, or user deleted it), the REPL MUST start with an empty module. [R4 S52]

### 15.3 Unified Development Model [R4 S52]

This design unifies interactive and file-based development:
- Interactive definitions are source files that happen to be managed by the REPL.
- File watching (§14) applies uniformly — external edits to the backing file MUST be picked up by the watcher and recompiled.
- The object cache (§14.7) accelerates both imported modules and the user's own work.

### 15.4 Regeneration Integrity [Tested tests/repl_persist::persist_user_cl_is_valid_source_with_topological_ordering]

The regenerated source file MUST satisfy the following invariants:

1. **Round-trip correctness:** Loading the regenerated file through the compiler MUST produce the same types, values, and module exports as the interactive session. [R4 S52]
2. **Authorship ordering:** Definitions MUST appear in the order they were registered with the session — file-loaded modules in source declaration order; REPL-introduced symbols appended in the order they were entered. Redefinition MUST NOT reorder; a redefined symbol keeps its original position. Cranelisp's cluster-atomic typecheck handles forward references natively, so dependency ordering is not a correctness requirement — the regenerated file reflects authorship intent. [R4 S52]
3. **Symbol qualification preservation:** The regenerated source MUST preserve the user's original qualification style. If the user wrote a fully-qualified reference (`core.option/Some`), it MUST remain fully-qualified. If the user wrote a bare name (`Some`) that was resolved via an import, it MUST remain bare. The regenerator MUST NOT rewrite bare names to qualified or vice versa. [R4 S52]
4. **Structural sections at top in fixed order:** Structural sections MUST appear at the top of the regenerated file in this fixed order: (a) platforms — `(declare-platform ...)` forms; (b) submodules — `(mod ...)` declarations; (c) exports — `(export ...)` forms; (d) imports — `(import ...)` forms. Within each section, items appear in authorship order (file parse order + REPL append). Definitions follow the four structural sections. [R4 S52]
5. **Comments:** The behaviour of comments in regenerated source is unspecified. The implementation MAY strip comments, preserve them, or handle them in any other way. [R4 S52]
6. **Source in cache metadata:** The `.meta.json` cache file MUST include all source text needed for regeneration, so that the REPL can restore the backing file from cache alone. [R4 S52]
7. **Authorship-intent rationale:** The regeneration invariants above (authorship ordering, fixed structural-section order, redef in place) collectively express a single intent — *principle of least surprise*. The regenerated file is a faithful record of what the user typed and when, not a derived form computed from compilation properties. The compiler's pipeline already handles forward references and dependency resolution; regeneration's job is authorship fidelity, not re-deriving correctness. [R4 S52]

### 15.5 File Watching Integration [R4 S52]

The file watcher (§14) MUST ignore writes triggered by the REPL's own source regeneration. Self-triggered writes MUST NOT cause a recompilation cycle. External edits to the backing file (e.g. from a text editor) MUST be detected and recompiled normally. [R4 S52]

### 15.6 Redefinition [Tested tests/repl_lifecycle::redefinition_replaces_value]

When the user redefines a name that already exists in the session, the regenerated source file MUST contain only the latest definition — the previous definition MUST be replaced, not duplicated. [R4 S52]

The runtime semantics of redefinition — dependent recompilation on signature-changing edits, the cascade report, broken symbols, and frozen-world behaviour for pre-break closure values — are specified in §18. The persistence interaction (restoring a session that contains broken symbols) is §18.8. [S101]

## 16. Test Discovery and Execution [R4]

The REPL provides commands for discovering and running test functions. Test infrastructure rests on two ordinary `primitives`-module entries — `discover-tests` and `catch-runtime-error` — plus the existing macro system. Both parse as plain applications, type by ordinary scheme resolution, and require import or FQ reference like any other `primitives` name (zero frontend and zero typecheck special-casing). Everything above them — selection, filtering, iteration, result interpretation, reporting, timing — is ordinary in-language code in the stdlib.

See `design/arch/test-discovery.md` (SETTLED, fourth convergence) for the full subsystem design.

### 16.1 Test Function Convention

A **test function** is any zero-argument function whose name begins with `test-` and whose return type is exactly `(Fn [] (Option String))`:

- `None` — the test passed
- `Some(reason)` — the test failed, with a human-readable reason string

There is no module naming requirement. Test functions may be defined in any module. A `test-`prefixed function whose scheme is not exactly `(Fn [] (Option String))` is **excluded from discovery and warned** at discovery time, so a mistyped test cannot silently masquerade as "no failures."

### 16.2 Slash Commands

#### 16.2.1 `/run-tests [module]` [R4]

Discover and run test functions. With no argument, searches the current module. With a module path argument, searches that module. The command is sugar over the in-language runner (§16.5).

```
user> /run-tests
  test-add ................................ ok
  test-div-zero .......................... FAILED: expected error

1 passed, 1 failed in 2.34ms
```

```
user> /run-tests user.math.test
  test-factorial ......................... ok

1 passed in 0.45ms
```

On failure, the trace tree for the failing test MUST be displayed after the failure reason (see §16.4).

#### 16.2.2 `/run-all-tests` [R4]

Discover and run all test functions in all loaded modules whose source files are under the project root. Library modules (discovered through the lib search path) are excluded.

```
user> /run-all-tests
  user/test-add .......................... ok
  user.math/test-factorial ............... ok
  user.io/test-read ...................... FAILED: file not found

2 passed, 1 failed in 5.67ms
```

### 16.3 The Primitives

`discover-tests` and `catch-runtime-error` are ordinary `primitives`-module symbols — imported (or FQ-referenced) like any other primitive, not special forms and not always-in-scope root names.

**`discover-tests`** — discovery primitive:

```
discover-tests              :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; current module
discover-tests "mod.path"   :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; named module (String arg)
discover-tests ["a" "b"]    :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; union over a Vec of module paths
```

Returns one `(Pair name callable)` per eligible `test-*` function:

- **`name`** — the fully-qualified test name `"module/test-name"` as a `String`, for selection, sorting, and reporting.
- **`callable`** — a language fn value of type `(Fn [] (Option String))` that, when invoked, performs a **GOT-slot-indirect call** to the test. The wrapper closes over the test's GOT slot, not a baked code pointer, so a *redefined* test runs its current body.

**Freshness.** The callables are late-bound GOT-slot wrappers. Calling `discover-tests` again re-scans live state: a `test-*` defined after a previous call is included on the next call, and a redefined test runs its new body. Selection and reporting compose over these values and stay fresh by construction — freshness lives in the returned values, not in expansion timing. (This is why discovery returns callables, not a `(Vec String)` of names threaded through a macro runner, which would freeze the test set at the macro's expansion time. The macro-runner approach is retired.)

The three call shapes are one underlying extern taking `(Vec String)`; the no-arg form (current module) and single-`String` form are stdlib-macro sugar normalising to the `Vec` form. The module argument is an ordinary value — a `String` or a `(Vec String)`, not a bare module path.

`Pair` and `Result` are seeded as primitives bootstrap types (alongside `Option`), so both are available to discovery results and to `catch-runtime-error`.

**`catch-runtime-error`** — protected-call combinator:

```
catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))
```

Promoted out of the test feature to a standalone `primitives` entry usable by any user code and by the stdlib — it is the language's only way to turn a runtime panic into a value. It invokes the thunk on the calling thread; if the thunk hit a language-level runtime error (match non-exhaustion, division by zero, vec out-of-bounds), it clears the error slot and returns `(Err message)`; otherwise it returns `(Ok result)`.

`TestResult`, `TestPass`, `TestFail`, and `run-test` are **retired**: a test's outcome is its own `(Option String)` (`None` = pass, `Some reason` = fail); the FQ name lives in the discovered `Pair`; timing comes from `trace`'s nanos.

### 16.4 Tracing Failures

The slash commands do NOT automatically trace failing tests. To trace a failing test, use `(trace (test-fn))` at the REPL:

```
user> /run-tests
  test-factorial ......................... FAILED: expected 120, got 0

0 passed, 1 failed in 1.23ms
user> (trace (test-factorial))
;; => Trace ADT with full call tree
```

Trace and test are independent, composable features — the user decides when tracing overhead is worthwhile.

### 16.5 Programmatic Use

The in-language runner is ordinary code — no macro. `discover-tests` returns `(name, callable)` pairs; `catch-runtime-error` brackets each callable; the runner folds a three-way outcome per test over the resulting `(Result (Option String) String)`:

- `(Err msg)` — the test panicked (match non-exhaustion, div-by-zero, …)
- `(Ok None)` — the test passed
- `(Ok (Some why))` — the test ran and reported an assertion failure

```clojure
(import [primitives [discover-tests catch-runtime-error]])

;; Run one discovered test: returns a human-readable line.
(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err msg)        (str-concat name " PANIC: " msg)]
       [(Ok None)        (str-concat name " ok")]
       [(Ok (Some why))  (str-concat name " FAIL: " why)])]))

;; Run every test in the current module.
(defn run-all []
  (map run-one (discover-tests)))

;; Run only the tests whose name contains a substring — selection is in-language,
;; over the SAME pairs, and stays fresh because the callables are late-bound.
(defn run-matching [substr]
  (map run-one
       (filter (fn [p] (match p [(Pair nm _) (contains? nm substr)])) (discover-tests))))
```

`catch-runtime-error` is usable by any code, not just tests:

```clojure
(import [primitives [catch-runtime-error]])

;; Try a risky computation; recover with a default on panic.
(defn safe-div [a b]
  (match (catch-runtime-error (fn [] (/ a b)))
    [(Ok q)   q]
    [(Err _)  0]))           ; division by zero panicked — recover with 0
```

Standard library convenience functions (e.g., `format-test-run`, `failures-only`, `test-passed?`) MAY be provided in a `core.testing` module but are not required by this specification.

### 16.6 `--link` Interim Behaviour

`discover-tests` is **REPL / `--run` only**. A `--link` build of a program that calls `discover-tests` is accepted at compile time, but the missing host symbol surfaces as an unresolved-symbol failure at link/load (the standalone executable has no live session to scan). This is documented interim behaviour — no friendly rejection yet; a future sprint may add a diagnostic.

`catch-runtime-error`, by contrast, **works in all modes including `--link`**: it is a self-contained intrinsic (it calls a closure already present in the linked program and constructs a `Result` heap value — no live session needed). Error capture is a pure runtime capability available everywhere; discovery is a dev-session capability.

## 17. Embedded Agent Experience [S88]

This section is **additive and behaviorally feature-gated.** It specifies the user-visible experience of the optional embedded LLM agent — a development partner that lives inside the live REPL session (`design/arch/repl-embedded-agent.md`). **None of §1–§16 changes.** When the agent feature is compiled out, or built-in but dormant (§17.4), the REPL is byte-identical to the deterministic REPL §1–§16 describes — every requirement below that references the agent is gated on it being **both compiled-in and runtime-enabled**.

The agent extends the self-documentation principle (§4) into a conversational partner, but it does **not** replace, alter, or contend with the deterministic surface. Three invariants hold unconditionally:

- **The deterministic REPL is untouched.** Any complete form, slash command, or **known**-symbol introspection routes exactly as §1–§16 specify, whether or not the agent is enabled (§17.1). The agent is a new destination for input the deterministic REPL would otherwise present as a parse error or an **unbound**-symbol display (genuine parse errors and bare *unknown* symbols/prose, §17.1) — and for the explicit `/ask` door — nothing more.
- **Everything the agent does is a visible REPL line.** The agent has no private capability surface: its reads, its proposed writes, and its shell proposals all appear as ordinary REPL commands and ordinary REPL output (§17.2). The session remains a legible, replayable script (§15).
- **Deterministic output and model output are unmistakable.** The agent's *prose* is rendered in a distinct reserved visual frame (§17.2); the deterministic `:Type value` format and the `;`-comment drawer remain exclusively the deterministic REPL's (§1, §4).

### 17.1 Agent Dispatch — The Classifier From the User's POV [S88]

When the agent is enabled, the REPL classifies each completed line of input into one of the existing deterministic destinations or the agent, **without regressing any §4 self-documentation behavior.** The classifier is a routing decision made one step earlier than evaluation; it does not change what any deterministic destination does.

**Parseable is not sufficient.** The discriminator is **symbol resolution**, not merely whether the reader accepts the input. The naive rule "anything the reader accepts routes deterministically" is wrong about the reader: multi-word natural-language prose (e.g. `how do I define a constrained function over Num?`) parses cleanly as `Ok(N bare symbols)` — a sequence of valid atoms — so a reader-acceptance test would route real sentences to the REPL, not the agent. The classifier therefore goes one step further: when a line parses to **bare atoms**, it **resolves** each symbol against the session before deciding. Known names stay deterministic (§4 is preserved); any unbound/unknown symbol routes the line to the agent. [S88]

A line is routed as follows (the first matching rule wins):

| Input shape | Routes to | Behavior |
|---|---|---|
| Starts with `/` (slash command) | Deterministic REPL | Unchanged (§3). `/ask` is the one slash command that forces the agent — see below. |
| `/ask <text>` | **Agent (always)** | The explicit door. Routes `<text>` to the agent unconditionally — **regardless of resolution** — bypassing the classifier (see below). |
| Blank or comment-only | Deterministic REPL | Unchanged — silent re-prompt (§2.3). |
| `parse(line)` → unclosed `(` or `[` (brackets not balanced) | Continuation | Unchanged — continuation prompt (§2.2). |
| `parse(line)` → a **genuine parse error** (stray `)`, unterminated string — *not* an unclosed bracket) | **Agent** | The text is sent to the agent as a natural-language turn. |
| `parse(line)` → `Ok(forms)` containing a **compound form** (`(…)` list or `[…]` vector) | Deterministic REPL | It is code. Expressions, definitions, special-form calls — evaluated/introspected exactly as today (§4, §1). |
| `parse(line)` → `Ok(forms)` of **bare atoms only**, where **every** symbol resolves (a literal, or a known/bound symbol) | Deterministic REPL | The §4 self-documentation surface is preserved: bare `map`, `+`, `42` are still **described** (§4), never sent to the agent. |
| `parse(line)` → `Ok(forms)` of **bare atoms** where **any** symbol is unbound/unknown | **Agent** | A bare `yes`, a typo like `lenght`, or any natural-language prose (a run of bare symbols, at least one of which is unknown) reaches the agent. |

**Symbol resolution is the discriminator.** For the bare-atom case the classifier consults the **same symbol table the §4 self-documentation uses** to describe a name. If the line is a single bare symbol or a run of bare symbols and **all** of them resolve (literals always resolve; known operators, builtins, special forms, types, traits, macros, and user/imported bindings resolve), the line is deterministic and is described/evaluated exactly as today. If **any** bare symbol is unbound, the line routes to the agent. This is why a bare known `map` is still described by §4, while a bare unknown `yes` — or a real sentence, which is just a run of bare symbols at least one of which is unknown — reaches the agent with no sigil. [S88]

**§4 self-documentation is preserved for known symbols.** A bare known symbol (`+`, `map`, `42`, a user-defined `foo`) routes to **introspection** (§4) and is **described**, not sent to the agent. The resolve→agent routing fires only on *unknown* symbols, so no input that §4 describes today changes destination. [S88]

**The explicit `/ask` door always reaches the agent.** `/ask <text>` routes `<text>` to the agent **unconditionally**, bypassing the classifier and ignoring resolution. This is the canonical way to ask the agent about a *known* symbol's usage in prose (e.g. `/ask how do I use map with a closure?` — where `map` is bound and would otherwise be described by §4), or to force a single bound word or a form-shaped question to the agent. [S88]

**Feature-off and dormant behavior (byte-identical fallback):**

- The resolve→agent routing is **entirely feature-gated.** When the agent is **compiled out** or **dormant** (built-in but no runtime key, §17.4) the classifier's `Agent` arm does not exist, and routing is **byte-identical to today**:
  - A bare unbound symbol → today's **"unbound" introspection display** (§4.1.10) — exactly as the deterministic REPL shows now. The resolution check still happens; it simply routes the unbound result to the §4 unbound display rather than to a nonexistent agent. [S88]
  - A genuine parse error (or a run of bare symbols including an unbound one) → today's **parse-error / unbound display** (§5.1, §4.1.10) — byte-identical to the deterministic REPL with no agent. [S88]
  - `/ask <text>` MUST print a single, clear notice and re-prompt — `agent not built in` when compiled out, or `agent not enabled (no key configured)` when built-in but dormant — and MUST NOT crash, evaluate, or alter session state. [S88]

This fallback is the user-facing guarantee behind "feature-off ⇒ the REPL is the original REPL": no input that routes deterministically today changes, and the only new behavior is the `Agent` arm, which is absent unless the agent is live.

### 17.2 Agent Output Frame — Prose vs. Commands [S88]

When the agent takes a turn, its output has two kinds, rendered differently so the user can never confuse model output with deterministic output:

1. **Agent prose** — the model's natural-language explanation, reasoning, or proposal text. This MUST be rendered in a **distinct reserved visual frame** (§10.3 "Agent prose frame" role): a left gutter marker (`▌`) prefixing each prose line, with the gutter in bright magenta when colour is enabled. The frame MUST degrade gracefully: under `--no-color`, `NO_COLOR`, or a non-TTY (§10.1), the gutter marker MUST still be emitted as a plain-text prefix (so the prose remains visually distinguishable in piped output and the showcase), but with no SGR codes. The prose frame is the **only** place the agent's own words appear; it MUST NOT use the `:Type value` format or the `;`-comment drawer (those belong to the deterministic REPL). [S88]

2. **Agent-issued commands and their results** — when the agent reads (`/source foo`, `/info bar`, `/refs baz`) or proposes a write or shell command (§17.7), the command line and its output render in **NORMAL deterministic REPL style** (§1, §3, §10) — exactly as if the user had typed them. They ARE normal REPL output (`design/arch/repl-embedded-agent.md` §4.4). The command appears echoed as a REPL line (so the user watches the agent reach for the introspection vocabulary and learns it by observation), and its result uses the result's normal role (cyan type prefix, dim comment drawer, the `/list` layout, etc.). These MUST NOT be wrapped in the prose frame. [S88]

The contract: **only the agent's prose is framed; everything the agent does deterministically is unframed and indistinguishable from a user keystroke's output.** This makes the deterministic-vs-model boundary unmistakable in every rendering mode. [S88]

A turn therefore reads on screen as an interleaving of framed prose and unframed REPL lines — e.g. a prose sentence, then an echoed `/source` line and its normal output, then more prose, then a proposed `(defn …)` shown (not submitted) as a normal definition echo. The whole interleaving is part of the replayable transcript (§15). [S88]

### 17.3 Consent Model [S88]

The agent's actions are gated by **what they touch**, not by which "mode" the user selected. The S88 MVP is **read-only Advise**: it reads and shows, and it MAY *propose* code (shown, never submitted), but it performs no writes. The fuller consent model (Build and Document writes) is specified here as the **target** for the agentic-Phase-2 work (S89); the S88 MVP implements only the read-only row. **S89 realizes the Build and Document write rows** — the Build confirm-gate UX is §17.14, the Document consultative-edit UX is §17.15; both extend (never relax) the "auto-approve reads only" floor.

| Action class | Consent | S88 MVP | Notes |
|---|---|---|---|
| **Reads** (`/source`, `/info`, `/doc`, `/refs`, `/exports`, spec lookups, …) | **Auto-run-and-show** — no confirmation | **Yes** | The default is "auto-approve reads only." Reads are side-effect-free introspection; they run and their output appears as normal REPL lines (§17.2). |
| **Build writes** (submit a `defn`/`deftype` into the session) | **Confirm-and-show** — the exact line is shown and the user approves before it is submitted | **No (S89)** | In the MVP the agent **proposes** code: the `(defn …)` is *shown* as a normal definition echo but **not submitted** (§17.3.1). The confirm-each-submission flow lands in Phase 2. |
| **Document writes** (set/replace a docstring or a module preamble, §17.5) | **Consultative** — the agent asks ("shall I record that as `solver`'s preamble?") before writing | **No (S89)** | The read of a preamble is an auto-run read (above); *writing* one is consultative and is Phase 2. |
| **Shell** (`/sh …`) | **Confirm-and-show** — the agent proposes the exact command; the user approves | **No (S89)** | The agent has no direct shell tool; shell is reachable only by proposing a `/sh` line the user must approve (§17.7). |

**The default is "auto-approve reads only."** No write of any kind — code, documentation, or shell — happens without an explicit user action in the turn. [S88]

#### 17.3.1 The MVP "proposed, not submitted" Read-Out [S88]

In the S88 read-only MVP, when the agent answers a request that warrants code, it MUST present the proposed code as a **normal definition echo** (the same rendering a user-typed `(defn …)` produces visually) inside the turn, and MUST make clear in its framed prose that the code is a **proposal the user can submit**, not something already in the session. The session symbol table MUST be unchanged by the proposal — typing the proposed name afterward MUST still report it as unbound (§4.1.10) until the user actually submits it. [S88]

This satisfies the Stage C acceptance shape: `/ask "how do I define a constrained function over Num?"` → a spec-grounded, session-aware answer with a proposed `(defn …)` **shown, not submitted.** [S88]

### 17.4 Opt-In-Twice and Dormancy [S88]

The agent requires **two** independent opt-ins to be live, and is **dormant** unless both hold (`design/arch/repl-embedded-agent.md` §7.3/§7.4):

1. **Compiled in** — the binary was built with the agent feature. A default build has no LLM client in it at all; `--agent` is a no-op (§0.6.1).
2. **Runtime-enabled with a key** — the session was started with the agent on (§0.6.1) AND a backend key/config is present.

Absent either, the agent is dormant: `/ask` reports the dormant case (§17.1) and prose falls back to the parse-error display. This is the user-facing expression of "off by default; the REPL works fully without it." A dormant or absent agent MUST never transmit anything anywhere. [S88]

### 17.5 `/doc <module>` and the Module-Preamble Edit UX [S88]

A **module preamble** (`spec/08-modules.md §8.16`) is module-level documentation — the leading `;;` comment block at the head of a module file, the module analogue of a `defn` docstring. The REPL surfaces it on the same introspection family as docstrings.

#### 17.5.1 Reading a Module Preamble — `/doc <module>` [S88]

`/doc` is overloaded by what its argument resolves to:

- `/doc <name>` — when the argument is a **definition** (function, type, trait, macro, …), reads that definition's **docstring** (the existing behavior, §3.1, §11.2.4). Unchanged.
- `/doc <module>` — when the argument resolves to a **module**, reads that module's **preamble** text (`spec/08-modules.md §8.16.4`). [S88]

The module-preamble read MUST:

- Print the preamble text. The text is presented as documentation prose, not as source comments — the stored form (§8.16.2) has the `;;` markers already stripped — so the user sees the documentation content directly, consistent with how `/doc <name>` shows a docstring's content (not its surrounding quotes). [S88]
- Indicate clearly when the module has **no preamble** — the module-level analogue of a definition with no docstring (§8.16.4). The no-preamble indication MUST be distinguishable from "module not found" (a resolution error per §3.5) and from an empty-but-present preamble. A module with no leading comment block is the common, valid case (§8.16.1) and MUST NOT be reported as an error. [S88]
- Resolve the module argument using the same logic as `/exports <module>` (§3.5) — submodule paths, root modules, stdlib modules; load-on-demand if not yet loaded; `Module '<name>' not found` if unresolvable. [S88]

Suggested shape (illustrative; the exact framing is at implementation discretion within these requirements):

```
user> /doc solver
; module solver
Sudoku solver: constraint propagation +
backtracking over a Vec-backed grid.

user> /doc util
; module util — no preamble
```

The `; module <name>` header and the no-preamble line are comment-drawer lines (`;`-prefixed, dim per §10.3), consistent with the self-documentation comment convention (§1.5). The preamble body is plain prose. [S88]

**Ambiguity note.** When a name could denote both a definition and a module (rare), `/doc` SHOULD prefer the definition reading and offer the module reading via the fully-qualified module path, OR clearly indicate which it resolved. The implementation MUST NOT silently pick one with no signal to the user. [S88]

#### 17.5.2 Module-Preamble Edit UX (read now; consultative edit in S89) [S88]

The preamble is **editable in-session** (`spec/08-modules.md §8.16.5`): setting or replacing a module's preamble rewrites the leading comment block in the module's backing file, and the change MUST round-trip byte-stably through source regeneration (§8.16.5; coordinated with the FIXME 0423 regen fix). The S88 work specs the **read** (§17.5.1) and the **shape** of the edit UX; the edit flow itself is the agent's **Document mode**, which is **consultative** and lands in S89 (§17.3).

The edit UX shape (normative on the experience when implemented in S89; specified now so the read and the edit are designed together):

- A preamble edit is a **Document write** — consultative (§17.3). The agent (or a user-facing edit command) MUST present the **exact new leading comment block** it proposes and ask for confirmation ("shall I record that as `solver`'s preamble?") before writing. [S88]
- On confirmation, the new preamble is rendered as the canonical leading `;;` comment block (§8.16.1) at the head of the module file; the rest of the file MUST remain byte-stable (§8.16.5). Setting a preamble on a module that had none inserts the block; clearing one removes it. [S88]
- An unmodified preamble MUST NOT be reflowed, re-wrapped, or re-marked on any regeneration (§8.16.5) — the user MUST be able to trust that source regeneration after an unrelated change leaves their hand-written preamble verbatim. [S88]
- The edit is shown as a normal REPL line (§17.2) and becomes part of the replayable transcript (§15). [S88]

Because the preamble is also the agent's primary durable memory (`design/arch/repl-embedded-agent.md` §3.1), improving a module's documentation and growing the agent's memory are the **same activity** — the user benefits from every preamble the agent helps write. [S88]

### 17.6 Reverse-Query Commands — `/refs` and `/tests-for` [S88]

These commands answer **reverse** questions (which sites reference X?) that the existing introspection family — all **forward** (name → sig/doc/source) — cannot. They are **LLM-free**, available in the **default build** (no agent feature required), and useful to humans directly. They exist because the agent needs them and "the agent's needs are also a human's" (`design/arch/repl-embedded-agent.md` §4.4 corollary) — the agent is a forcing function that grows the REPL's introspection vocabulary for everyone. [S88]

Both are an **on-demand scan over the in-memory bodies** of the live session — no maintained reverse index, no cache to invalidate in a mutating session. (The implementation strategy is `/int`-owned; the spec pins the user-visible result + format.) [S88]

#### 17.6.1 `/refs <sym>` [S88]

`/refs <sym>` lists the **definitions in scope whose body references `<sym>`** — the call/use sites of a symbol. [S88]

- The argument is required. `/refs` with no argument MUST print a usage hint: `Usage: /refs <symbol-name>`. [S88]
- The output lists the referencing definitions by their fully-qualified name, using the **same normative layout algorithm** as `/list` (§3.3 rules L0–L4) — names only — so `/refs` output is consistent with the rest of the introspection family and stays byte-identical to `/list` for the same name set. [S88]
- If no definition in scope references `<sym>`, print a clear no-results line (e.g. `; no references to <sym>`), distinguishable from an unknown-symbol error. [S88]
- If `<sym>` is itself an unbound name in the session, `/refs` SHOULD report `unbound symbol '<sym>'` (consistent with §4.1.10) rather than silently reporting no references — distinguishing a typo from a genuinely-unreferenced symbol. [S88]

```
user> /refs grid-get
; references to grid-get
solver/solve solver/propagate
user> /refs unused-helper
; no references to unused-helper
```

#### 17.6.2 `/tests-for <sym>` [S88]

`/tests-for <sym>` lists the **test functions whose body references `<sym>`** — "what tests exercise this?" A test function is one recognized by the test convention (the `test-` prefix and the test signature, §16.1). [S88]

- The argument is required. `/tests-for` with no argument MUST print a usage hint: `Usage: /tests-for <symbol-name>`. [S88]
- The output lists matching test functions by fully-qualified name, using the `/list` layout (§3.3 L0–L4), byte-identical for the same name set. [S88]
- If no test references `<sym>`, print a clear no-results line (e.g. `; no tests reference <sym>`), distinguishable from an unknown-symbol error. This is itself useful signal — an un-tested symbol. [S88]

```
user> /tests-for solve
; tests referencing solve
solver/test-solve-easy solver/test-solve-hard
```

Both commands MUST appear in `/help` (§3.2) and MUST NOT crash or alter session state on any input (§5.2). [S88]

### 17.7 Shell Proposals [S88]

The agent has **no direct shell tool.** When the agent would run a shell command, it MUST do so by **proposing a `/sh <cmd>` line** (§13) that the user approves — confirm-and-show (§17.3). The agent proposes the exact command (shown as a normal REPL line, §17.2); the user runs it. This is **S89** (a write-class action); the S88 read-only MVP issues no shell proposals. [S88]

### 17.8 Privacy and First-Use Disclosure [S88]

The agent's view is bounded by the introspection surface and the embedded spec — **not** the host filesystem (no raw file-read tool; §17.6's scans are over in-memory session structures, not files). When the agent is enabled and a turn would transmit data to the backend, the REPL MUST satisfy the **opt-in-twice** discipline (§17.4) and the **first-use disclosure** below.

#### 17.8.1 First-Use Disclosure — Normative Wording [S88]

The **first time** in a session that the agent would transmit anything to the configured backend, the REPL MUST present a one-time disclosure **before** the transmission, stating plainly **what is sent** and **to where**. The disclosure is normative in content (the exact phrasing is at implementation discretion, but it MUST convey all of the following):

- **What is sent** — the disclosure MUST state that the following leave the session and are sent to the backend:
  1. **The user's message** (the `/ask` text or the prose that routed to the agent).
  2. **Harvested source excerpts** — explicitly **source excerpts, not merely signatures.** The disclosure MUST use language that makes clear the *bodies* of code are transmitted, not only type signatures. Per the agent's context model (`design/arch/repl-embedded-agent.md` §4.3), the harvested context includes the **full source of the current module** and the **full source of recently-mentioned functions** (the last ~10), plus module preambles and export surfaces. The wording MUST NOT understate this as "signatures" or "metadata" — it MUST say source excerpts / code bodies. [S88]
- **To where** — the disclosure MUST name the **configured endpoint** (the backend the session is configured to use) so the user knows the destination of the transmitted data. [S88]

Illustrative wording (an implementation MAY reword, but MUST cover every element above):

```
▌ Heads up — the embedded agent is about to contact an external model.
▌ What is sent: your message, plus source excerpts harvested from your
▌ session — including the full source of the current module and of the
▌ functions you have recently referenced (their code bodies, not just
▌ their type signatures), and module documentation.
▌ To where: <configured-endpoint>.
▌ (The agent is dev-session only and never runs in --run or --link.
▌  To keep the agent off, restart without --agent, or start with --no-agent.)
```

The disclosure MUST appear in the agent prose frame (§17.2) so it is unmistakably the agent's own notice. It is shown **once per session** before the first transmission; subsequent turns do not repeat it. An implementation MAY additionally require an explicit per-session acknowledgement before the first transmission; if it does, declining MUST keep the agent dormant for the session with no transmission. [S88]

The disclosure's honesty about **source excerpts** is the user's only signal that their code bodies — not just abstract type information — are leaving the machine. Understating it would be a conformance failure, not a wording nicety. [S88]

### 17.9 Relationship to the Deterministic Spec [S88]

This section is the **complete** set of additive agent requirements on the REPL experience. The deterministic contract (§1–§16) is unchanged; the only deterministic-surface additions are:

- the `/ask`, `/refs`, `/tests-for` command rows and the `/doc <module>` overload (§3.1);
- the `--agent` / `--no-agent` flags (§0.6.1) and (S89) the `--yes` / `-y` flag (§0.6.2);
- the "Agent prose frame" style role and (S89) the "Agent-input prompt" style role (§10.3);
- (S90) the `/syntax` command row (§3.1, §17.17) and the `/search` command row (§3.1, §17.19, *design-pinned re-pin*) — both reusing existing §10.3 roles, **no new style role**.

The **S90** additions (§17.17–§17.21 — the fluency pillars) introduce **no new style role**. Two of the four are **non-agent, default-build** surfaces (the command rows above) and two stay *inside* the agent surface: `/syntax` (§17.17) is an LLM-free static-asset command that also serves as an agent pull-tool; the signature-grain harvest (§17.18) is ambient agent context with **no command and nothing extra in the REPL**; `/search` (§17.19) is a **non-agent-gated default-build session facility** (re-pinned 2026-06-23 — its background index is built by the nice workers, which run regardless of the `agent` feature; the agent merely reaches it through the ordinary pull) and is **design-pinned-now / implemented-later** (gated on the FIXME-0432 fix + the nice-worker `catch_unwind` floor per §11.3); and the silent agent log (§17.20) is an env-opt-in (`CRANELISP_AGENT_LOG`), feature-gated, off-by-default file sink that produces **nothing extra in the REPL**. Its **companion**, the persistent full-content trace (§17.21, `CRANELISP_AGENT_TRACE=<path>` — re-purposed from S89's ephemeral stderr trace, whose stderr sink is **removed**), is a sibling env-opt-in, feature-gated, off-by-default file sink with the **identical silent/graceful contract**; the two are joined by a shared `turn` key. The **byte-identical-feature-OFF** invariant therefore scopes to the agent-gated surfaces (the harvest, the log, and the trace all require the agent); `/syntax` and `/search` are present and functional in the default build. [S90 re-pin]

The **S89** additions (§17.12–§17.16) are all *inside* the agent surface — the agent-input prompt (§17.12) and markdown/fenced-Lisp rendering (§17.13) only ever affect agent-issued/agent-turn output, and the Build confirm-gate (§17.14), Document consultative edit (§17.15), and the `--yes` auto-accept (§17.14.5 / §17.15.2a) + autonomous-submit first-use notice (§17.16) only fire when the live agent proposes a write. `--yes` (§0.6.2) is, like `--agent`, a no-op on default builds and when no agent is active. None alters the deterministic REPL: feature-off or dormant, no agent line is issued, no agent prose is rendered, and no write gate exists, so §1–§16 stay byte-identical. [S89]

Of these, `/refs`, `/tests-for`, and `/doc <module>` are **LLM-free** and live in the default build; `/ask`, the agent frame, and the agent flags are **feature-gated** and inert (or accepted-but-no-op) when the agent is compiled out. The resolution-aware dispatch classifier (§17.1) — which resolves bare atoms and routes any *unknown* symbol to the agent — is itself **entirely feature-gated**: feature-off, an unbound bare symbol still lands on today's §4.1.10 unbound display and a genuine parse error on the §5 display, so the REPL is byte-identical to §1–§16. [S88]

### 17.10 Enabling & Configuring the Agent [S88]

This subsection is **normative** on how a user turns the agent on and points it at a backend. It pins the as-built scheme: the agent is a **compile-time feature** plus **environment-based runtime configuration** — and it is **explicitly NOT configured via `Cranelisp.toml`** (see the rationale below).

#### 17.10.1 Enabling — the `agent` Cargo feature [S88]

The embedded agent is compiled **only** when the binary is built with the `agent` Cargo feature, which is **off by default**:

- A **default build** (`cargo build`, `cargo nextest run`) contains no LLM client at all — the entire `src/agent/` module is absent. `/ask` reports `agent not built in` (§17.1) and `--agent` is an accepted no-op (§0.6.1). This is the first of the two opt-ins (§17.4).
- An **agent build** (`cargo build --features agent`) compiles the agent in. Whether it is *live* in a given session still depends on the runtime configuration below — being compiled in is necessary but not sufficient (opt-in-twice, §17.4). [S88]

#### 17.10.2 Configuring — the environment, NOT `Cranelisp.toml` [S88]

The agent is configured **entirely through environment variables**, read once at session construction. The agent **MUST NOT** read `Cranelisp.toml` (the project config file) for provider, model, or key. [S88]

**Rationale (normative intent).** The provider, model-id, and API key are **per-developer secrets and preferences**, not version-controlled project configuration. `Cranelisp.toml` is checked into the project and shared across every developer and CI run; an API key there would be a leaked secret, and a hard-coded provider/model there would impose one developer's backend choice on the whole team. Keeping agent configuration in the environment keeps secrets out of source control and lets each developer (and each shell session) choose their own backend independently. The agent therefore **never** consults `Cranelisp.toml`. [S88]

The environment surface (matching the as-built `src/agent/provider.rs`):

| Variable | Meaning | Default |
|---|---|---|
| `CRANELISP_AGENT_PROVIDER` | Selects the backend: `anthropic`, `ollama`, or `stub`. | `anthropic` [S88] |
| `CRANELISP_AGENT_MODEL` | The model-id (provider-specific). **Required** for any live provider — a live provider with no model-id stays dormant. | — [S88] |
| `ANTHROPIC_API_KEY` *or* `CRANELISP_AGENT_KEY` | The Anthropic API key. Its **presence** (non-empty) is the reachability gate for the Anthropic provider; either variable supplies it. | — [S88] |
| `OLLAMA_API_BASE_URL` | The Ollama endpoint. Ollama needs **no key** — it is the local / offline escape hatch (the U6 privacy path, §17.8). | `http://localhost:11434` [S88] |
| `CRANELISP_AGENT_STUB_SCRIPT` | **Test-only.** Path to a scripted-response fixture for the deterministic `stub` provider. This selects a canned, offline test double — it is **not** an end-user configuration knob. | — [S88] |

#### 17.10.3 Dormancy — the reachability gate [S88]

With the feature compiled in (§17.10.1) but **no provider configured or reachable**, the agent is **dormant** (§17.4) — it never transmits anything (§17.8). This is the **second** opt-in: the agent is live only when it is *both* compiled in *and* backed by a configured, reachable provider. [S88]

When the agent is dormant for want of configuration, `/ask` MUST report what to set, naming the missing variables for the selected provider — for example:

- Anthropic (the default provider) with no key or no model-id → a notice to set `ANTHROPIC_API_KEY` (or `CRANELISP_AGENT_KEY`) **and** `CRANELISP_AGENT_MODEL`. [S88]
- Ollama with no model-id → a notice to set `CRANELISP_AGENT_MODEL` (no key is needed for Ollama). [S88]

The reachability gates are, per provider: **Anthropic** — a non-empty key *and* a non-empty model-id; **Ollama** — a non-empty model-id (the endpoint defaults to localhost, no key); **stub** — a loadable fixture from `CRANELISP_AGENT_STUB_SCRIPT`. Absent its gate, each provider yields a dormant agent rather than an error, and `/ask` renders the dormant notice (§17.1) naming what to set. [S88]

#### 17.10.4 Cross-reference — the first-use disclosure [S88]

Configuration determines **where** data goes, so it is bound to the privacy disclosure (§17.8). The **first** time a live agent would transmit in a session, the REPL presents the first-use disclosure (§17.8.1) naming the **configured endpoint** — i.e. the backend selected by `CRANELISP_AGENT_PROVIDER` and its endpoint. Because **Ollama is local** (`OLLAMA_API_BASE_URL` defaults to `http://localhost:11434`), a turn against an Ollama backend transmits to the local host and **nothing leaves the machine** — the offline escape hatch (§17.8). A turn against the Anthropic provider transmits source excerpts to the external Anthropic endpoint, which is exactly what the §17.8.1 disclosure exists to surface. [S88]

### 17.11 Debugging the agent context — `/context` [Tested+Neg tests/agent.rs::context_feature_off_prints_not_built_in, tests/agent.rs::agent_on_context_dumps_request_to_file_dormant] [S88]

`/context <path>` is a **debug command** for inspecting *what the agent would send the model* — not for invoking it. It writes the agent's **fully assembled next-turn request** — byte-for-byte the grounding, context, and turn structure that an `agent_turn` would transmit on the next turn — to the file at `<path>` as readable text, and **does not call the model**. Its purpose is to let a developer audit the agent's grounding, harvested context, and system primer **offline**, before (or without) ever spending a transmission. [S88]

**What it dumps.** The file contains the assembled request rendered as labelled sections, in **send-order** — the order in which the material is presented to the model: [S88]

```
=== BUDGET (approx) ===
=== SYSTEM PRIMER ===
=== HARVESTED CONTEXT ===
=== TOOLS (read-only) ===
=== TRANSCRIPT ===
=== CURRENT USER TURN ===
```

- `=== BUDGET (approx) ===` — the approximate token/size budget for the turn. [S88]
- `=== SYSTEM PRIMER ===` — the agent's system grounding (its role, the introspection vocabulary, the consent model). [S88]
- `=== HARVESTED CONTEXT ===` — the context the agent harvested from the live session (the in-memory introspection surface and embedded spec excerpts, §17.8) for this turn. [S88]
- `=== TOOLS (read-only) ===` — the tool surface offered to the model. In the S88 read-only MVP this is the read-only pull allowlist (§17.3); `/context` itself is **not** in it (see below). [S88]
- `=== TRANSCRIPT ===` — the conversation so far this session. [S88]
- `=== CURRENT USER TURN ===` — the pending user turn that would be sent next. [S88]

**Works dormant/offline — no model call, no key.** Because `/context` dumps the *assembled* request rather than transmitting it, it functions regardless of provider, reachability, or dormancy (§17.4, §17.10.3): it requires **no API key and contacts no backend**, and a **dormant** agent (built-in but unconfigured) MUST still produce the full dump. This is the entire point — the developer can inspect grounding, harvest, and primer **without** opting in to a transmission. A dormant agent dumping its context does **not** violate "a dormant or absent agent MUST never transmit anything" (§17.4): writing a local file is not a transmission. [S88]

**Human-only debug command — never an agent tool.** `/context` is invoked **only by the human** at the prompt. It is **NOT** in the agent's pull allowlist (§17.3) and the agent **cannot** issue it — `/context` writes a file, which is outside the agent's read-only capability surface (§17.2, §17.8). It does not appear in the `=== TOOLS (read-only) ===` section it dumps. [S88]

**Success and error reporting.** On success the REPL prints a confirmation line naming the path and the number of characters written — e.g. `wrote agent context to <path> (<N> chars)`. If `<path>` cannot be written (e.g. an unwritable directory), the REPL reports a graceful error rather than crashing or panicking. [S88]

**Feature-OFF behavior.** When the binary is built **without** the `agent` feature (§17.10.1), `/context` prints `agent not built in` — identical to `/ask`'s feature-off behavior (§17.1) — and writes nothing. [S88]

### 17.12 Agent-Input Prompt — Who Typed What [S89]

§17.2 establishes that an agent turn interleaves **framed prose** (`▌` gutter) with **unframed deterministic REPL lines** (the agent's reads, proposals, and — in S89 — its writes, all rendered as if the user had typed them). That unframed-equals-keystroke contract created an honesty gap surfaced in live S88 use: when the agent **issues a line itself** — a pulled read command (`/source foo`), or (S89) a submitted form — the line renders with **no prompt prefix at all**, so a reader scanning the replayable transcript (§15) cannot tell whether the agent typed it or the user did. This subsection closes that gap with a distinct **agent-input prompt**. [S89]

**The agent-input prompt glyph.** Every line the agent "types" — i.e. a line the *agent originated* and the REPL is echoing as an issued command — MUST be prefixed with a distinct **agent-input prompt**: the token `agent>` (the agent analogue of the human `user>` prompt, §2.1). The prompt:

- is **distinct from the human prompt** (`user>` / the timing+module prompt of §2.1) — the reader can tell agent-issued input from user-typed input at a glance; [S89]
- is **distinct from the `▌` prose gutter** (§17.2) — a pulled command is the agent *acting*, not the agent *speaking*; the `agent>` prompt marks issued input, the `▌` gutter marks prose. The two never share a glyph. [S89]
- is styled per the new §10.3 "Agent-input prompt" role (dim, with the `agent` token in bright magenta to tie it visually to the agent's magenta prose frame), and **degrades under `--no-color`, `NO_COLOR`, or a non-TTY** (§10.1) to the **plain-text token `agent>`** with no SGR codes — so piped output and the showcase still read honestly. [S89]

**Where the agent-input prompt appears (the two agent-echo sites).** The `agent>` prompt prefixes exactly the lines the agent issues as input:

1. **Pulled read commands** (§17.2) — when the agent reaches for `/source`, `/info`, `/refs`, `/sig`, … the echoed command line carries `agent>`; its **result** below it renders in normal deterministic style (cyan type prefix, dim drawer, the `/list` layout — §1, §3) exactly as today, *unprefixed and unframed*. Only the issued command line gets the `agent>` prompt; the result is the REPL's own output. [S89]
2. **Build-submit echoes** (§17.14) — when the agent submits a form past the confirm-gate, the submitted definition line is echoed with `agent>` so the transcript shows the agent issued it (then the normal `:Type name` definition result follows, unprefixed). [S89]

Illustratively (colour elided):

```
user> /ask how does grid-get work?
▌ Let me look at its definition.
agent> /source grid-get
:(Fn [primitives/Vec primitives/Int] primitives/Int) solver/grid-get  ; defn - Read a cell
▌ It indexes the flat grid vector by row-major offset. ...
```

The `agent>` line is agent-issued input; the `:(Fn …)` line beneath it is the deterministic REPL's normal `/source` output; the `▌` lines are the agent's prose. Three visually-distinct origins, each honestly marked. [S89]

**Feature-off / dormant.** The agent-input prompt exists only when the agent is live (it only ever prefixes agent-issued lines, which only exist when the agent takes a turn). Feature-off or dormant, no agent line is ever issued, so the prompt never appears — the deterministic REPL is byte-identical (§17.1, §17.9). [S89]

### 17.13 Markdown Rendering Within the Agent-Prose Frame [S89]

The agent returns **markdown** prose. S88 rendered it raw inside the `▌` frame (§17.2) — headings, lists, emphasis, and fenced code all passed through verbatim, and (the live-use defect, §17.13.3) raw ANSI escape codes could leak as literal text. S89 specifies that the model's markdown is **formatted for the terminal inside the §17.2 prose frame**, that fenced Lisp renders through the deterministic pretty-printer, and — normatively — that **no raw ANSI escape code ever appears as literal text** in any rendering mode. [S89]

#### 17.13.1 Markdown Formatting (inside the `▌` frame) [S89]

The agent's prose MUST be formatted as terminal text — not emitted as raw markdown source — **within** the §17.2 agent-prose frame (every formatted prose line still carries the `▌` gutter; the markdown formatting lives *inside* the frame, not beside it). The formatter MUST handle the common markdown the model actually produces:

- **Headings** (`#`, `##`, …) — rendered as a visually-distinct heading line (e.g. bold), not as a literal `## ` prefix. [S89]
- **Bullet and numbered lists** — rendered as aligned list items with a bullet/number marker, not as literal `- `/`1. ` source. [S89]
- **Emphasis** — `**bold**` and `*emphasis*` rendered with the corresponding terminal weight/style (bold, italic), with the surrounding `*`/`**` markers consumed (not shown literally). [S89]
- **Inline code** — `` `code` `` rendered as a distinguishable inline span (e.g. via the existing palette), with the backticks consumed. [S89]

This is a **bounded** terminal formatter for the markdown the model emits — not a full CommonMark engine; constructs it does not handle MUST degrade to readable plain text (the marker shown or stripped), never to a crash or to garbled output. The formatting uses the **existing §10.3 palette roles** (bold, dim, etc.) — it introduces **no new colour and no new style role** beyond the agent-prose frame role already in §10.3. [S89]

**Degrades cleanly under `--no-color`.** Under `--no-color`, `NO_COLOR`, or a non-TTY (§10.1), the markdown formatting MUST degrade to **plain text with the `▌` gutter still present** (per §17.2's frame-degradation rule) and **no SGR codes** — headings/lists read as plain text lines, emphasis markers are stripped to their words, inline code shows its text. The prose stays legible and frame-marked in piped output and the showcase, exactly as the bare prose did in S88. [S89]

#### 17.13.2 Fenced Lisp Renders via the Pretty-Printer [S89]

When the model's prose contains a fenced code block whose info-string is `lisp` (or `cranelisp`) — `` ```lisp … ``` `` — the block's body MUST be rendered through the **deterministic S-expression pretty-printer** (the same printer `/source` and `/sexp` use, §3.1, §10) — syntax-highlighted and indented — **not** emitted as a raw fence. The pretty-printed block renders **inside** the `▌` prose frame (it is part of the agent's *answer* — the agent *showing* code — distinct from an agent-issued `/source` pull, which is the agent *running a command* and renders unframed with the `agent>` prompt, §17.12). A fence with a **non-Lisp** info-string (e.g. `` ```sh ``) is left as a literal block (markdown-formatted, not pretty-printed). [S89]

The pretty-printed fence MUST honour the colour mode: syntax-highlighted when colour is enabled, plain indented text under `--no-color`/non-TTY — degrading via the **same** global colour gate as every other styled output (§10.1, §10.7), never a separate one. [S89]

#### 17.13.3 No Raw ANSI Escape Codes — Normative (the S88 defect) [S89]

In live S88 use, agent output sometimes emitted ANSI colour codes as **literal text** (e.g. a visible `\033[36m…` in the rendered prose or a fenced block) instead of rendering as colour. This is a **conformance failure**, not a cosmetic nicety. Normatively:

- In **every** rendering mode, an agent turn's output (framed prose, formatted markdown, and pretty-printed fenced Lisp) MUST contain **no ANSI escape code as literal visible text**. Colour codes either take effect as styling (colour enabled) or are absent entirely (colour disabled) — they are never shown as characters. [S89]
- Under `--no-color`, `NO_COLOR`, or a non-TTY (§10.1), agent output MUST be **completely free of SGR/escape sequences** — the `--no-color` transcript is clean plain text (gutter + plain prose + plain-indented Lisp). [S89]
- This is the **user-visible acceptance** for the defect's fix: an `/ask` answer containing prose **plus** a `` ```lisp `` block renders with formatted prose and a pretty-printed, correctly-coloured form, with **no literal escape codes anywhere**, and stays clean under `--no-color`. [S89]

(The root cause is an int-internal render-path wiring issue — style-once-at-the-leaf, the global colour gate honoured uniformly — not a missing colour-mode parameter; that is `/int`/`/dev`-owned mechanism. This spec pins only the user-visible contract: no literal escapes, clean `--no-color`. A `/qa` narrow failing-not-ignored repro is owed before closure, per `CLAUDE.md §Testing`.) [S89]

### 17.14 Build Mode — The Confirm-Gated Submit UX [S89]

S88's read-only MVP **proposed** code — shown, never submitted (§17.3.1). S89 promotes the agent to **propose-then-submit-on-confirm**: the agent MAY submit a form into the live session, but **only past a confirm-gate the user controls**. This realizes the §17.3 "Build writes → confirm-and-show" row, which S88 specified as the target and left unimplemented. The read-only-by-default floor (§17.3) is **extended, not replaced**: a write is reachable **only** past the confirm-gate; reads stay auto-run-and-show; non-read, non-submit tools (e.g. `/sh`, §17.7) stay refused. [S89]

#### 17.14.1 The Confirm-Gate Experience [S89]

When the agent wants to submit a form, the user sees, in order:

1. **The proposed form, shown pretty-printed.** The exact `(defn …)`/`(deftype …)` the agent proposes is rendered as a normal definition echo (the same visual a user-typed definition produces, §1.3) — pretty-printed (§17.13.2) so the user reads exactly what would be submitted. It is echoed with the **`agent>` agent-input prompt** (§17.12) so it reads honestly as agent-issued. [S89]
2. **A confirm prompt.** The REPL MUST then present a clear, single-line confirm prompt that names the action as a **code submission** and offers an explicit accept/decline choice — e.g. `submit this definition? [y/N]`. The prompt MUST make the **default-decline** posture visible (the capitalized `N`): pressing Enter, or any non-affirmative response, declines. The exact wording is at implementation discretion but MUST convey (a) that a **definition is being submitted into the session**, and (b) an explicit yes/no with **decline as the safe default**. [S89]

The consent interaction is a **synchronous prompt at the REPL prompt** — the user types `y`/`n` (or equivalent) on the next line, the same way they answer any prompt; it is not a background dialog or a mode switch. [S89]

#### 17.14.2 Accept and Decline [S89]

- **On accept** (`y`): the form is submitted — it goes through the *same* path a user keystroke uses, so it is type-checked, defined, and persisted exactly as if the user had typed it, and its normal `:Type name` definition result (§1.3) renders **unframed** below the echo (it is now real session state). Typing the new name afterward reports it as bound (§4). The submission is part of the replayable transcript (§15). [S89]
- **On decline** (Enter / `n` / anything non-affirmative): **nothing is written to the session.** The proposal is discarded; the session symbol table is **unchanged** — typing the proposed name afterward MUST still report it unbound (§4.1.10), structurally identical to the S88 "proposed, not submitted" floor (§17.3.1). The agent is told the user declined (so it does not assume the code is live) and the turn continues. A decline MUST never partially apply, crash, or leave the session in an inconsistent state. [S89]

#### 17.14.3 The Pre-Flight Validator — The User Never Sees an Agent Compile Error [S89]

Before a proposed form reaches the confirm-gate (§17.14.1), the REPL **silently validates** it (a behind-the-scenes type-check on a throwaway staging copy) and, on **any** failure — a parse error or a type error, no distinction — **silently repairs** it (asks the model to fix it and re-validates), up to a bounded number of attempts. The user-visible contract (the U5 ratified decision, `design/arch/repl-embedded-agent.md §6.4`):

- **The user NEVER sees a raw agent compiler error.** A broken intermediate the agent generated — the broken form *and* the compiler diagnostic it produced — MUST NOT appear in the transcript at all. Only a form that **at least parses and type-checks** ever reaches the confirm-gate echo. The whole stage→check→discard→repair exchange is invisible. [S89]
- **No stack of compiler diagnostics, ever.** The user is never shown a sequence of failed attempts, error messages, or internal retry chatter. The validator's work is silent by construction. [S89]

#### 17.14.4 The Validator Give-Up Wording [S89]

If silent-repair exhausts its attempt cap without producing a form that validates, the agent **gives up gracefully** — it does **not** submit broken code, and it does **not** dump a compiler error. Instead it renders, in its prose frame (§17.2), a **single honest, polite notice** that it could not produce valid code here — e.g. *"I wasn't able to produce code that compiles cleanly for this — here's my best attempt, which you may need to adjust."* Normatively, the give-up:

- MUST be a **graceful, plain-language notice** in the agent prose frame — never a raw compiler diagnostic, a stack trace, or a stack of failed attempts. [S89]
- MUST NOT submit anything to the session (it degrades to the §17.3.1 read-only "proposed, not submitted" floor). [S89]
- MAY show its **last attempt clearly marked as an un-submitted proposal** the user can copy and hand-fix — pretty-printed (§17.13.2), with no confirm-gate (there is nothing valid to submit), and with prose that makes unmistakable it is **not** in the session. [S89]

The exact phrasing is at implementation discretion but MUST convey: it could not produce valid code, nothing was submitted, and (if shown) the remaining code is an unverified suggestion. The user's experience of an agent that cannot get the code right is a **calm apology and a suggestion**, never a wall of diagnostics. [S89]

#### 17.14.5 Autonomous Submit Under `--yes` — Auto-Accept the Confirm-Gate [S89]

When the session is started with `--yes` (§0.6.2), the Build confirm-gate (§17.14.1) **auto-accepts**: the agent submits its proposed form **without prompting** for `[y/N]`. Normatively:

- **The proposed form is still shown.** The pretty-printed `agent>`-prefixed definition echo (§17.14.1 step 1) MUST still render before submission — the user always sees exactly what the agent submitted. `--yes` removes the **question**, not the **visibility**. [S89]
- **The confirm prompt is suppressed; submission proceeds as on accept.** In place of the `submit this definition? [y/N]` prompt (§17.14.1 step 2), the form goes straight through the **accept path** (§17.14.2) — type-checked, defined, persisted, with its normal `:Type name` result rendered unframed below the echo, and added to the replayable transcript (§15). The behaviour is exactly as if the user had answered `y`. [S89]
- **The decline path is unreachable while `--yes` is on, by design.** There is no opportunity to decline an individual Build submit under `--yes`; that is the flag's purpose. (To regain per-action control, restart without `--yes`.) [S89]

#### 17.14.6 The Validation Floor Holds Under `--yes` — Never Submit Raw [S89]

`--yes` auto-answers **consent, not validation** (`/arch` ruling, `design/arch/repl-embedded-agent.md §7.4`). The pre-flight validator (§17.14.3) and its give-up path (§17.14.4) are **invariant under the flag** — `--yes` changes nothing about them:

- Every form the agent submits under `--yes` is **still silently validated and silently repaired** exactly as with `--yes` off (§17.14.3). Only a form that at least parses and type-checks is ever auto-submitted; a deliberately-broken generation is **silently repaired, never submitted raw.** The user never sees broken code reach the session, with or without `--yes`. [S89]
- If silent-repair exhausts its attempt cap, the agent **gives up gracefully** under `--yes` exactly as in §17.14.4 — it does **not** auto-submit broken code, and it does **not** dump a compiler diagnostic. `--yes` cannot force an un-validating form into the session; the give-up degrades to the read-only "proposed, not submitted" floor (§17.3.1), shown as an un-submitted suggestion. [S89]

`--yes` removes the prompt, not the correctness floor. An implementation that treated `--yes` as "skip the dry-run" would be a conformance defect (the `/arch` validation-floor invariant). [S89]

### 17.15 Document Mode — The Consultative Preamble/Docstring Edit UX [S89]

S88 specified **reading** a module preamble (`/doc <module>`, §17.5.1) and the **shape** of the edit UX, deferring the edit itself to S89 (§17.5.2). S89 specifies the **edit experience**: the agent records its understanding durably — as a module preamble or a definition docstring — through a **consultative** gate that is deliberately distinct, in wording and posture, from the Build code-submit confirm (§17.14). This realizes the §17.3 "Document writes → consultative" row. [S89]

#### 17.15.1 The Consultative Gate — Distinct From the Build Confirm [S89]

A Document write (set/replace a module preamble or a definition docstring) is **consultative**, not a terse code-submit confirm. The two write classes are distinguished **by the question the user is asked**, so the user always knows whether the agent is changing **code** or changing **documentation**:

- **Build (code) — confirm posture** (§17.14): `submit this definition? [y/N]` — a terse, default-decline confirm for a code change. [S89]
- **Document (documentation) — consultative posture**: the agent **proposes recording its understanding** and asks a consultative question naming the target — e.g. *"record this as `solver`'s preamble?"* (for a module preamble) or *"record this as `grid-get`'s docstring?"* (for a definition docstring). The wording is a **consultation** ("shall I record this as …?"), distinct from the Build "submit this definition?" — the user is being asked to endorse a piece of *documentation*, not to approve *code*. [S89]

Before asking, the agent MUST **show exactly what it proposes to record** — the proposed preamble/docstring text, rendered as it would be stored (for a module preamble, the canonical leading `;;` comment block, §17.5.2; for a docstring, the docstring text) — so the user endorses the exact wording. The proposal echo carries the `agent>` agent-input prompt (§17.12). [S89]

#### 17.15.2 Accept and Decline [S89]

- **On accept**: the preamble/docstring is written durably into the code — for a module preamble, as the canonical leading `;;` block at the head of the module's backing file (§17.5.2); for a docstring, into the definition. The edit is shown as a normal REPL line (§17.2) and becomes part of the replayable transcript (§15). The **rest of the file MUST remain byte-stable** (§8.16.5) — an unrelated regeneration MUST leave the hand-written text verbatim (the §17.5.2 no-reflow guarantee). [S89]
- **On decline**: nothing is written; the existing preamble/docstring (or its absence) is unchanged; the agent is told the user declined and the turn continues. [S89]

#### 17.15.2a Autonomous Edit Under `--yes` — Auto-Accept the Consultative Gate [S89]

`--yes` (§0.6.2) is **blanket** — it auto-accepts the Document consultative gate (§17.15.1) as well as the Build confirm-gate (§17.14.5). When `--yes` is active:

- **The proposed text is still shown.** The agent MUST still render exactly what it proposes to record — the preamble `;;` block or the docstring, as it would be stored, carrying the `agent>` prompt (§17.15.1) — before writing. The user always sees the documentation the agent recorded. [S89]
- **The consultative question is suppressed; the edit proceeds as on accept.** In place of the *"record this as `solver`'s preamble?"* consultation (§17.15.1), the edit goes straight through the **accept path** (§17.15.2) — written durably into the code with the rest of the file byte-stable (§8.16.5), shown as a normal REPL line, added to the transcript. The behaviour is exactly as if the user had endorsed it. [S89]
- **The decline path is unreachable while `--yes` is on, by design.** No per-edit decline opportunity exists under `--yes`. (Restart without `--yes` to regain per-edit consultation.) [S89]

The byte-stable round-trip (§8.16.5) and the durable-memory promise (§17.15.3) hold unchanged under `--yes` — the flag removes the question, not the correctness or persistence guarantees.

#### 17.15.3 The Durable-Memory Promise — "Next Session It Remembers" [S89]

A Document edit is **durable**: it round-trips byte-stably through source regeneration (§17.5.2, §8.16.5) — the recorded text persists in the code exactly as endorsed. Because the agent's harvested context reads module preambles and docstrings back from the live session (§17.8, the agent's durable memory is the code, `design/arch/repl-embedded-agent.md §3.1`), a preamble the agent helps write **this** session is read back by the agent **next** session. The experience-level promise the user can rely on: **what the agent records, it remembers** — and because the record lives in the code as ordinary, readable documentation, improving a module's docs and growing the agent's memory are the **same activity** (§17.5.2). The user never maintains a separate agent memory; the documentation *is* the memory, and it is durable across sessions. [S89]

#### 17.15.4 Honest Failure — No False "Recorded" [Tested+Neg tests/agent.rs::set_doc_missing_target_e2e_refused_no_false_recorded_neg, tests/agent.rs::set_doc_non_function_target_e2e_refused_not_recorded_neg (agent-feature lane: cargo nextest run --features agent --test agent)]

The durable-memory promise (§17.15.3) only holds for a target the edit **can** record durably. When the proposed docstring target is **not durably recordable**, the Document edit MUST **fail honestly**: the agent surfaces a clear error naming why, MUST NOT claim it "recorded" anything, and MUST leave the live state unchanged (no ephemeral in-session write that vanishes on restart). The honesty contract has two faces, both of which are refusals — not silent no-ops:

- **Missing target ⇒ "no such definition".** A docstring edit names a symbol that has **no local definition** in the current module — including a never-defined name, a qualified `mod/sym`, or a name that is only a re-exported **import** (not a local `Def`) — is refused with a not-found error (e.g. `no such definition: <symbol>`). The agent does not guess and does not fabricate a target. [S94]
- **Non-recordable kind ⇒ refused, naming "function".** A docstring edit names a symbol that **does** resolve locally but is **not a user-defined function** (a primitive extern, an ADT constructor, a type — any kind whose docstring would display in-session but **not survive source regeneration**, §17.5.2) is refused with a message making clear that only a function's docstring can be recorded. Surfacing an in-session-only docstring that silently disappears on the next session would break the §17.15.3 promise, so it is refused rather than half-applied. [S94]

In both cases the failure reaches the user as the agent's own honest report (the U5 "never a raw compiler error" posture, §16.4); the consultative gate's success line (*"recorded …"*) MUST NOT appear, and a subsequent session's `/doc <symbol>` MUST show no spuriously-recorded docstring. This is the negative face of the durable-memory promise: the agent records what it **can** durably remember, and is honest about what it cannot. [S94]

### 17.16 Autonomous-Submit First-Use Notice — `--yes` Escalation Disclosure [S89]

`--yes` (§0.6.2) is an **autonomy escalation**: the agent now writes — submits Build forms (§17.14) and records Document edits (§17.15) — **without asking** the per-action `[y/N]`/consultative question. Parallel in spirit to the S88 transmit first-use disclosure (§17.8.1), this escalation warrants its own **one-time** notice (per the `/arch` ruling, `design/arch/repl-embedded-agent.md §7.4 (b)`; wording owned here).

The **first time** in a session that `--yes` is active and the agent **would write** (the first Build submit or Document edit), the REPL MUST present a one-time disclosure **before** the write, in the agent prose frame (§17.2) so it is unmistakably the agent's own notice. It is shown **once per session** — subsequent autonomous writes do not repeat it. The disclosure is **normative in content** (exact phrasing at implementation discretion, but it MUST convey all of the following):

- It MUST state that, because the session was started with `--yes`, the agent will **submit definitions and record documentation edits without asking** — the per-action confirm/consultative prompt is being **auto-accepted** on the user's behalf. [S89]
- It MUST state that the user **still sees every form and every edit** the agent makes (they are shown as agent-issued lines, §17.12) — autonomy removes the prompt, **not** the visibility. [S89]
- It MUST state that the **pre-flight validator still gates correctness** (§17.14.3): only code that compiles is ever submitted — `--yes` skips the question, **not** the correctness check; the agent never submits broken code. [S89]
- It SHOULD state how to regain per-action control: **restart without `--yes`.** [S89]

Illustrative wording (an implementation MAY reword, but MUST cover every element above):

```
▌ Autonomous mode (--yes) — the agent will submit definitions and record
▌ documentation edits WITHOUT asking you each time. You still see every
▌ form and edit it makes (shown as agent> lines). Only code that compiles
▌ is ever submitted — the pre-flight check still runs; --yes skips the
▌ prompt, not the correctness check.
▌ (To approve each write yourself, restart without --yes.)
```

An implementation MAY additionally require an explicit per-session acknowledgement before the first autonomous write; if it does, declining MUST fall back to the per-action confirm/consultative gates (§17.14.1 / §17.15.1) for the rest of the session (i.e. behave as if `--yes` were off). This disclosure is **distinct from** the §17.8.1 transmit disclosure — that one names *what leaves the machine*; this one names *that the agent acts without asking*. Both may fire in the same session (transmit first, then autonomous-write). [S89]

### 17.17 The `/syntax` Cheat-Sheet Command — Pillar 1 [S90]

S88/S89 made the agent *act*; the S90 fluency phase makes it *reach* for supplemental
detail rather than guess. The first reach is **`/syntax`** — a topic-indexed,
token-dense, **verified-compiling** reference for the **core language syntax**, surfaced
as a REPL command that is useful to **both the human at the prompt and the agent**
(the self-documenting-REPL principle, root `CLAUDE.md` §"Design Principles", turned toward
syntax discovery). It is the curated, higher-precision replacement for fuzzy spec-grep
(`design/arch/repl-embedded-agent.md §11` R7; `sprints/SPRINT.md §Pillar 1`). [S90]

**Ownership boundary (R7 — do not author content here).** This section specifies the
**command UX only**. The cheat-sheet **content** — the topic taxonomy and each topic's
verified-compiling examples — is **`/docs`-owned** (authored from `spec/`, validated by
`/spec`), shipped as a static `include_str!` asset (sibling to `primer.txt`,
`src/agent/`). The command-wiring (the `/syntax` `ReplCommand` variant + dispatch +
agent-tool allowlist row + the primer topic-name cross-reference) is `/dev (src/)`-owned.
`/syntax` **references** the topic vocabulary; it does **not** define it. [S90]

#### 17.17.1 The Two Forms — Bare List, Topic Detail [S90]

- **`/syntax` (bare)** — lists the **available topic names**, so a reader (human or agent)
  learns the vocabulary it can pull on. The output is a plain, scannable list of topic
  names (e.g. `hkt  defn-multi-sig  cond  match  traits  modules  annotations  let
  recursion-tco  …` — the exact set is `/docs`-owned). It MUST also name how to drill in:
  a one-line hint such as `Use /syntax <topic> for detail.` The bare list is the
  **index**, not the content. [S90]
- **`/syntax <topic>`** — returns that topic's **dense content**: a curated, mixed
  prose+form reference combining a compact explanation, syntactic **`FORM` templates**
  (e.g. `(defn name ([params] body) ...)` with `...` and metavariables), and one or more
  **verified-compiling** Cranelisp `EXAMPLE` lines. The asset is **rendered as authored —
  deterministic plain text, exactly the bytes shipped in the curated asset**. It is **not**
  routed through the S-expression pretty-printer: the `FORM` templates are syntactic
  skeletons, not parseable expressions, so the pretty-printer cannot consume them, and the
  concrete `EXAMPLE` lines are presented as-authored to preserve their layout. [S90 re-pin]
- **Unknown topic** — `/syntax <unknown>` MUST NOT error opaquely. It re-prints the
  available-topics list (as bare `/syntax` does) with a short note that the requested topic
  is not one of them — the self-documenting principle: a wrong topic name teaches the right
  vocabulary, never a dead end. [S90]

#### 17.17.2 Output Framing — Reuse Existing Roles, Degrade Cleanly [S90]

`/syntax` is **deterministic REPL output**, not agent prose — it is a static curated asset
read off disk, the same category as `/help` or `/list`. Accordingly:

- The topic's content is **emitted verbatim — deterministic plain text, exactly as authored
  in the curated asset**. It introduces **no new colour and no new style role**, and it does
  **not** route content through the pretty-printer or apply syntax highlighting to the
  example/form lines (§17.17.1). The bare-index headings and dim hints MAY use the existing
  §10.3 palette roles (the `/list`/`/help` family), but no new role is added. It is **not**
  wrapped in the `▌` agent-prose frame (§17.2) — that frame marks *model output*; `/syntax`
  content is curated, deterministic, and human-authored. [S90 re-pin]
- It **degrades under `--no-color`, `NO_COLOR`, or a non-TTY** (§10.1) to clean plain text
  with **no SGR codes** — the topic list reads as plain names, each topic's content as the
  authored plain text. Piped output and the showcase stay legible, exactly as `/list` does.
  Because the topic content is already plain text, `--no-color` and TTY output differ only in
  any framing (headings/hints), never in the body. [S90 re-pin]

> **Non-normative — possible future enhancement.** Syntax-highlighting the concrete
> `EXAMPLE` lines (the verified-compiling code) is conceivable later, but is **explicitly
> out of scope now**: the templated `FORM` lines are not parseable S-expressions, so the
> pretty-printer cannot render them, and the agent — the primary consumer — needs the dense
> text, not colour. Any future highlighting would have to discriminate `EXAMPLE` from `FORM`
> lines and would couple the renderer to the asset's content format; the modest gain does
> not justify it now. [S90 re-pin]

#### 17.17.3 Dual Use — Human Command and Agent Pull-Tool [S90]

`/syntax` is in the agent's **read-only pull allowlist** (§17.3) — the agent issues
`/syntax <topic>` to ground itself on a syntax point it does not know, exactly as it pulls
`/source` or `/info`. When the agent pulls it, the issued command line carries the
**`agent>` agent-input prompt** (§17.12) and its result renders **unframed** below — the
same who-typed-what honesty as every other agent pull (§17.12 site 1). Illustratively
(colour elided):

```
user> /ask how do I write a higher-kinded type?
▌ Let me check the exact syntax.
agent> /syntax hkt
<the hkt topic's dense, plain-text content as authored>
▌ So you'd write it like this: ...
```

The `agent>` line is agent-issued input; the content beneath it is the deterministic
`/syntax` output; the `▌` lines are the agent's prose — three honestly-marked origins
(§17.12). [S90]

**It is LLM-free.** `/syntax` is a static curated asset; it works **with the agent absent
or feature-off** — a human types `/syntax match` in a default (non-`agent`) build and gets
the cheat-sheet. (It is the agent's *pull surface* only when the agent is live; the command
itself is unconditional, like `/help`.) [S90]

#### 17.17.4 Relationship to the Primer Topic Cross-Reference [S90]

The always-on primer (`src/agent/primer.txt`) carries a **compact core-syntax summary that
cross-references the `/syntax` topic *names***, so the model knows *which topics exist* and
can pull detail on demand (R7; `repl-embedded-agent.md §11` item 1). The division of labour
the user experiences:

- the **primer** gives the model the always-needed essentials **plus the topic vocabulary**
  (a known list of names to reach for) — it does **not** inline every topic's full content
  (that would bloat every turn); [S90]
- **`/syntax <topic>`** is the **on-demand depth** the primer points at — pulled only for the
  few topics a given turn actually needs. [S90]

This is core-language syntax derived from spec — the primer-appropriate kind of grounding.
It does **NOT** hardcode prelude/stdlib idioms into the primer; those stay **harvest-sourced**
(§17.18, honouring the `agent-prelude-awareness-via-harvest-not-primer` ruling). The line:
**core syntax → primer summary + `/syntax` depth; prelude/stdlib symbols → harvest (§17.18)**.
[S90]

### 17.18 Ambient In-Scope Symbol Awareness — Harvest at Signature Grain — Pillar 2 [S90]

The harvester (§17.8, `design/arch/repl-embedded-agent.md §4.1`) already pushes the *shape*
of the session into every turn's context, silently and without being asked. S90 **enriches
its grain** so the agent has **ambient awareness of what is in scope** — the in-scope prelude
and imported symbols — at **name + full type signature + docstring** grain, every turn,
**without** the agent first having to spend a turn on `/imports`/`/list`/`/exports`. This is
the user-directed "keep prelude plus imported symbols in context" delivered the user-owned
way — **harvest, not primer** (`agent-prelude-awareness-via-harvest-not-primer`;
`sprints/SPRINT.md §Pillar 2`). [S90]

**This is ambient, not a command.** There is **no `/harvest` command** and nothing extra
appears in the human's REPL — the enrichment lives entirely in the context the agent
receives each turn (auditable offline via `/context`, §17.11, where it appears under
`=== HARVESTED CONTEXT ===`). The human-facing equivalents already exist and are unchanged:
`/imports` (§3.4) and `/list`/`/exports` (§3.3/§3.5) are how a *human* inspects in-scope
symbols; Pillar 2 gives the *agent* that same picture ambiently, at signature grain. [S90]

#### 17.18.1 The Display Grain — Name + Signature + Docstring [S90]

For each **in-scope** symbol — the current module's own definitions, the symbols the module
explicitly imports, **and** the implicit prelude symbols (the §3.4 "Prelude (implicit)"
surface when the prelude-fallback bit is on) — the harvested context surfaces **three facets
per symbol**:

1. **name** — the symbol as the agent would write it (bare when in scope; the reader already
   has the §3.4 import provenance), [S90]
2. **type signature** — the symbol's full type in the canonical cranelisp `:Type` notation
   (the same signature `/sig` and the bare-symbol lookup render, §4.1, §3.1) — fully-qualified
   type names, exactly as the REPL displays them, so the agent references the **actual**
   signature rather than guessing it, [S90]
3. **docstring** — the symbol's docstring when it has one (a defn docstring; a primitive's
   §A.5 Description, §3.1) — so the agent knows *what a symbol does*, not just its shape;
   absent when the symbol carries none (no placeholder). [S90]

This is **`/imports` + `/list` at signature grain** — the names those commands list, each
annotated with the signature and docstring a human would get by then typing the name. It is
a **read enrichment** of an existing harvest arm (the export-surface arm of `harvest_context`,
`src/agent/harvest.rs`) — the symbol table stays the single source of truth (Principle 7); the
harvest copies nothing, it reads grain it previously skipped. [S90]

#### 17.18.2 How It Reads In Context — and the Budget [S90]

The enriched in-scope block reads as a compact symbol-with-signature listing — conceptually
(the exact rendering is `/dev`-owned; this pins the grain and the read, not the bytes):

```
== in scope ==
solver/grid-get :: (Fn [primitives/Vec primitives/Int] primitives/Int)  ; Read a cell
+ :: (Fn [primitives/Int primitives/Int] primitives/Int)  ; primitive - integer addition
map :: (Fn [(Fn [a] b) (primitives/Vec a)] (primitives/Vec b))  ; apply f to each element
...
```

**Budget governs grain, as everywhere in the harvest (§17.8, `§4.2`).** Signature+docstring
grain is heavier than the bare export names §3.4 lists. The enrichment therefore rides the
**same graceful-degradation ladder** the harvester already enforces (`harvest.rs`, the
`char_budget` gate): under budget pressure the in-scope block degrades grain
(signature-without-docstring, then names-only) rather than being silently truncated to a
misleadingly-short list — the agent must never believe a symbol is *absent* merely because the
budget elided its detail. The acceptance is experiential: **a fresh agent session references an
in-scope symbol's actual signature without first having to `/list`/`/exports`** (`SPRINT.md
§Pillar 2 acceptance`). [S90]

### 17.19 Importable-Symbol Search — `/search` — Pillar 3 (DESIGN-PINNED, IMPLEMENTED LATER) [S90 re-pin]

> **Status: RE-PINNED, DESIGN-ONLY THIS SPRINT, IMPLEMENTED LATER.** Pillar 3 was
> redesigned mid-plan (user, 2026-06-23); the authoritative architecture is
> `repl-embedded-agent.md §11.1–§11.9` (commit `c699045`). The command was **renamed
> `/lib-search` → `/search`** (R12), is now a **non-agent-gated default-build session
> facility** (R9), searches symbols reachable on the **lib search path ∪ the project root**
> (R10), matches by **name OR scheme, exact OR partial on both axes** (R6), and is served by
> an **eager-but-triggered** background index built by the nice workers (R4/R9b). Per the
> `/arch` Phase-2 ruling (R1; `repl-embedded-agent.md §11.5`), Pillar 3 still ships as
> **design only** in S90 — implementation is gated on the FIXME-0432 typecheck root fix
> **plus** the nice-worker indexer `catch_unwind` floor (CF.2, §11.3). This subsection pins
> the **experience contract** — the command shape, the result row, the dual human/agent use,
> the partial-result UX, and the safety floor — so the implementation, whenever it lands, has
> a fixed target. It carries the `[S90 re-pin]` tag and is **not yet a conformance MUST** for
> a shipping build. [S90 re-pin]

Pillars 1 and 2 ground the agent in the **core language** (`/syntax`) and **what is already
in scope** (harvest). Pillar 3 closes the last fluency gap: discovering symbols that are
**reachable but not yet imported** — "importable", not yet in scope — by **name and/or type
signature**. This is the experience of *"is there already a function that does this?"*
answered **before** writing the `(import …)`, for both the human and the agent. [S90 re-pin]

**Reachable scope (R10).** `/search` searches symbols reachable on the **lib search path ∪
the project root** that are **not yet imported** into the session — the same file-resolution
rules `import` uses. Already-imported, in-scope symbols are surfaced by Pillar 2 (harvest,
§17.18) and the deterministic `/list` family; `/search` covers what is *importable but not
yet in scope*. [S90 re-pin]

**A normal session facility, not an agent feature (R9).** `/search` is an **ordinary
default-build REPL command** — it works in **every** REPL session, with or without the
`agent` feature. The background index that serves it is built by the **nice workers** (the
low-priority background threads that already do object-file codegen), which run regardless of
the `agent` feature. The agent reaches `/search` through the **ordinary
tools-as-visible-REPL-commands pull** (§17.3 / R11), exactly like `/syntax`, `/list`, or
`/exports` — there is **no special agent path** to it. The byte-identical-feature-OFF framing
that governs the agent-gated pillars (§17.1, §17.17) therefore does **not** apply to
`/search`: it is present and functional in the feature-OFF build. [S90 re-pin]

The mechanism is **typecheck-to-index-then-discard** served from a background index
(`§11.1–§11.2`): to know an importable symbol's signature, its defining module must be
typechecked, but it must **not** be imported into the session — so the nice-worker indexer
typechecks reachable modules into throwaway staging, reads out their public symbols into two
derived lookup indices (name and scheme), and **discards** the typecheck state, serving
searches from the indices. That seam is **int/typecheck-owned** (`§11.1–§11.4`); this section
owns only the **user-visible** half. [S90 re-pin]

#### 17.19.1 The Command Shape — `/search <query>` [S90 re-pin]

`/search <query>` searches the importable-symbol indices and lists matching symbols. The
query is matched (per R6, `§11.4`) by either axis, **exact OR partial**:

- **by name** — `/search <name>`. **Exact** name match, plus **partial** = case-insensitive
  **substring** of the symbol name (e.g. `/search grid` finds `grid-get`, `grid-set`,
  `make-grid`); and/or [S90 re-pin]
- **by scheme** — `/search <scheme>`. **Exact** scheme match (the query type-shape matches an
  indexed signature **up to alpha-renaming of type variables**, e.g. `/search (Fn [Int Int]
  Int)` finds symbols of exactly that shape), plus **partial = structural-contains** — the
  query type-shape appears as a **sub-structure** of a candidate's scheme up to alpha-renaming
  (e.g. `/search (Vec Int)` matches a symbol of scheme `(Fn [(Vec Int)] Bool)`; `/search Int`
  matches any scheme mentioning `Int`). This structural-contains partial match is the target
  (`§11.4`); full Hoogle-style subsumption (a query `(Fn [Int] ?)` *subsuming* `(Fn [Int]
  Bool)` with hole-instantiation + ranking) is a **`/typecheck`-owned follow-up**, and the
  **query-pattern syntax for holes/wildcards** is a **flagged `/spec` consult** (R6, `§11.4`)
  — *not* specified here. [S90 re-pin]

How an implementation distinguishes a name query from a scheme query (e.g. a leading `(Fn …`,
or an explicit flag) is at implementation discretion, but the command MUST support **both**
axes and **both** exact and partial matching on each. An empty or no-match query re-prompts
with a short "no importable symbols matched" note (self-documenting; never an opaque error).
[S90 re-pin]

#### 17.19.2 The Result Row — Name, Signature, Module, How-To-Import [S90 re-pin]

Each result row MUST show enough for the reader to **decide and act** — four facets:

1. **symbol name** — the importable symbol; [S90 re-pin]
2. **type signature** — its full `:Type` signature (canonical cranelisp notation, FQ type
   names, §4.1) — the same grain Pillar 2 surfaces for in-scope symbols, so search results and
   in-scope listings read identically; [S90 re-pin]
3. **originating module** — the module the symbol lives in (its full path), so the reader knows
   *where it comes from*; [S90 re-pin]
4. **how to import it** — the exact `(import …)` form that would bring it into scope (e.g.
   `(import [solver.grid [grid-get]])`) — so a human can copy-paste it and the agent can
   propose-and-submit it (Build mode, §17.14) directly. This is the actionable payoff:
   search → see the form → import. [S90 re-pin]

Conceptually (rendering `/dev`-owned; this pins the facets):

```
user> /search (Fn [Int Int] Int)
grid-get :: (Fn [primitives/Int primitives/Int] primitives/Int)
  in solver.grid   — (import [solver.grid [grid-get]])
gcd :: (Fn [primitives/Int primitives/Int] primitives/Int)
  in math.number   — (import [math.number [gcd]])
```

Results use the **existing §10.3 palette roles** (the `/list` family) and **degrade under
`--no-color`/non-TTY** (§10.1) to clean plain text — same rule as `/syntax` (§17.17.2) and
every other deterministic command. [S90 re-pin]

#### 17.19.3 Eager-But-Triggered Index — Partial Results While Indexing [S90 re-pin]

The background index is **eager-but-triggered** (R4/R9b): it is **not** built unconditionally
at session start (a session that never searches and never starts the agent should not pay the
cost of typechecking the whole lib-path ∪ project-root). The nice workers **arm** the index on
the **first `/search`** (human or agent pull) **or first agent activation**; once armed they
**race ahead** — burning down the reachable-module worklist eagerly, not one module per query.

Because the burn-down may still be in progress when a `/search` lands, the experience contract
is **partial-results-plus-a-note**: a `/search` issued before indexing completes MUST serve
the matches found **so far** and append a short progress note — `indexing N modules…` (or
equivalent) — telling the reader the result set is incomplete and more may appear if the
search is repeated. This is the same self-documenting, never-opaque posture as every other
deterministic command: a not-yet-complete index is a transient state surfaced plainly, not an
error and not a silent empty result. A subsequent `/search`, once the burn-down has advanced,
returns the fuller set. [S90 re-pin]

#### 17.19.4 Dual Use — Human Command and Agent Pull-Tool [S90 re-pin]

`/search` is both a **human REPL command** (typed at the prompt to find a library function
before importing) and an **agent read-only pull-tool** (§17.3) — the agent issues `/search …`
to discover a reachable symbol it needs, exactly as it pulls `/syntax` or `/exports`, through
the **same ordinary tools-as-visible-REPL-commands pull** every other command uses (R11);
there is no agent-specific search path. When the agent pulls it, the issued line carries the
**`agent>` prompt** (§17.12) and the result renders **unframed** below. The command is a
**normal default-build facility** (the index is deterministic and built by the nice workers;
the command works with the agent absent — §17.19 preamble, R9). The natural agent workflow the
dual use enables: *search → find the symbol + its import form → propose the import (and the
using code) through the Build confirm-gate (§17.14)* — fluency end-to-end, from "is there a
function for this?" to a submitted, importing, type-checking form. [S90 re-pin]

#### 17.19.5 Robustness — Searching the Library Must Never Crash the REPL [S90 re-pin]

Because Pillar 3 typechecks **arbitrary reachable third-party modules** at index time, a
malformed or 0432-shaped reachable module on the lib-path ∪ project-root could (today, in a
debug build) **crash a worker by being indexed** (`§11.3`). The experience contract, pinned
now for the later implementation: **`/search` MUST NOT crash the REPL or the session**, and
indexing MUST NOT silently degrade the session, regardless of what a reachable module contains.
A reachable module that fails to typecheck (or trips a compiler `debug_assert!`) MUST be
**silently skipped** — it is simply **absent from results** — never an unwound worker thread, a
panic, or a lost session. The skip is a search-quality note (logged, optionally surfaced as
"could not index <module>"); the bad module never enters the indices and never reaches the
reader as an error. (The two-layer containment that makes this hold — the `/typecheck` 0432
root fix plus the **nice-worker** `catch_unwind` floor, CF.2 — is `§11.3`-owned mechanism;
this pins only the user-visible floor: **searching the library is always safe**.) [S90 re-pin]

### 17.20 Silent Agent Activity Log — Pillar 4 [S90]

Pillar 4 is a **two-sink** recording surface: a compact, greppable **index** (this log, §17.20)
and a full-content **trace** (§17.21), joined by a shared `turn` key (§17.21.3). This section
specifies the **index** half: a **silent, persistent, structured** log of the agent's activity,
written to a **file**, with enough structure to **`grep`/`jq` "where did the agent struggle"** by
hand — the *recording* half of self-tuning, captured now so insight can be extracted manually (and
automated later) (`sprints/SPRINT.md §Pillar 4`; `repl-embedded-agent.md §11.6`, R5). The `/arch`
ruling makes it a **new feature-gated sibling sink** (`src/agent/log.rs` / the reserved
`telemetry.rs` slot); its content companion, the full-content trace, **re-purposes** S89's
`CRANELISP_AGENT_TRACE` from an ephemeral stderr view into a persistent file sink (§17.21). This
section owns the **`/repl` experience details** of the index — that it is silent, where it goes,
its format, and the `turn` key it shares with the trace. [S90]

#### 17.20.1 Silent — Nothing Extra in the REPL [S90]

The log is **SILENT**: writing it produces **nothing extra in the REPL** — no banner, no
"logging to …" line, no per-event echo, no change to any transcript. The human's session looks
**byte-identical** to the same session with logging off; the agent's framed prose, its `agent>`
lines, and its results are exactly as specified in §17.1–§17.19. The log is a **dev-session
artifact** (NG4, `repl-embedded-agent.md §1.3`) — it is written **off to the side**, never
surfaced, and (like the whole agent) never present in a `--link`/`--release` artifact. [S90]

#### 17.20.2 Env-Configurable Location — Sibling to `CRANELISP_AGENT_TRACE` [S90]

The log is **opt-in via an environment variable**, a sibling to the §17.10.2 agent env surface
and to `CRANELISP_AGENT_TRACE`. The normative `/repl` recommendation:

| Variable | Meaning | Default |
|---|---|---|
| `CRANELISP_AGENT_LOG` | Path to the agent activity-log file. **Set** ⇒ the agent appends one structured record per event to this file. **Unset/empty** ⇒ **no log is written** (the default — silent *and* absent). | — (unset = off) [S90] |

Rationale and rules:

- **Off by default, opt-in by setting a path.** Like every agent knob (§17.10.2), it is an
  environment variable, **not** `Cranelisp.toml` (a log path is a per-developer dev-session
  preference, not version-controlled project config). Unset ⇒ no file is created and no logging
  cost is paid. Naming it after a **path** (rather than a `=1` toggle) makes the destination
  explicit and lets each developer/session direct its own log. [S90]
- **Append, persistent, across turns and the session.** When set, each agent event appends to
  the file (the file persists; it is the durable record across the whole session, unlike the
  ephemeral trace). [S90]
- **Feature-gated; absent on the default build.** Like `CRANELISP_AGENT_TRACE` and the whole
  agent, the log exists **only** in an `--features agent` build; on a default (non-`agent`)
  build the variable is inert and **no log is ever written** (feature-OFF stays byte-identical,
  §17.9). [S90]
- **Graceful on an unwritable path.** If `CRANELISP_AGENT_LOG` names a path that cannot be
  written, the agent MUST **degrade silently** — it does **not** crash the session, and
  (consistent with §17.20.1) it does **not** spew errors into the REPL. Logging is a side
  channel; its failure never disturbs the session. [S90]

#### 17.20.3 Format — Persistent JSONL, Greppable by Hand [S90]

The log is **JSONL** — one JSON object per line, one line per agent event — chosen precisely so
`grep`/`jq` extract insight **without a query UI** (`SPRINT.md §Pillar 4`). The **`/repl`
experience requirement** is that the format carry **stable, greppable keys** for the
struggle-signal the user wants to mine — at minimum: an **event type** (e.g. a model exchange, a
pull, a **validator-repair iteration**, a submit/commit, a give-up), the **symbol** involved when
there is one, an **error class** for a repair iteration (the triggering compiler error), a
**repair-iteration count**, the **module**, and a **`turn`** correlation key (§17.21.3) — the
per-turn/exchange index shared with the full-content trace (§17.21) so each compact log line
**joins** to the trace exchange that produced it. (The exact key vocabulary the loop emits is
`/dev`-owned — it consumes the events `pull.rs`/`run_pull`/`run_submit` already produce; this
pins the *experience* requirement: the keys are stable enough that a one-line `grep`/`jq`
extracts "every repair event and its triggering symbol/error" reliably.) The acceptance is
operational: **`grep`/`jq` over the file extracts the repair events and exploration pulls with
their triggering symbols/errors** (`SPRINT.md §Pillar 4 acceptance`). [S90]

The log **stays the compact index** — it carries *metadata-only* keys (event/symbol/error_class/
iteration/module/`turn`) and **no content** (no form text, no error message, no model prose). It is
the **greppable index** that tells you *where* the agent struggled; the full **content** of each
exchange lives in the companion trace sink (§17.21), joined by the shared `turn` key (§17.21.3). Do
**not** thicken the log with content fields — its grain is deliberately thin so a one-line `grep`/`jq`
stays fast and the file stays scannable. [S90]

This log is the **passive recording** half only. The **automated curation/push loop** that would
read it back to curate the primer/cheat-sheet — plus the §4.7/U4 push-transparency header — is
**deferred** (`SPRINT.md §Out of scope`): capture the signal now, extract insight by hand, automate
once the pattern proves worth it. [S90]

### 17.21 Persistent Full-Content Agent Trace — `CRANELISP_AGENT_TRACE=<path>` — Pillar 4 (companion) [S90]

The §17.20 log is metadata-only — too thin, on its own, to extract insight (it names *where* the
agent struggled, not *what* it said or saw). Its companion is the **trace**: a **persistent,
full-content** transcript of every agent exchange — the assembled request and the model's
response — written the same env-path way, **joined to the log by a shared `turn` key** (§17.21.3).
Together they form **two complementary sinks**: the log is the compact **index** (grep to *find*
the trouble spot); the trace is the full **content** (read *what* was sent and returned there). [S90]

This **re-purposes** S89's `CRANELISP_AGENT_TRACE` (`src/agent/trace.rs`). Today that variable is an
**ephemeral stderr** debug view that **truncates** each form/message to ~80 chars — fine for watching
one turn live, useless as a durable record. The new normative behaviour: `CRANELISP_AGENT_TRACE` names
a **path**, and the agent appends the **full, untruncated** transcript to that file. **The stderr sink
is removed** — there is no longer any `eprintln!` trace view; the trace is **path-only**. [S90]

#### 17.21.1 The Contract — Identical to `CRANELISP_AGENT_LOG`, Full-Content Payload [S90]

`CRANELISP_AGENT_TRACE` is a **sibling sink** to `CRANELISP_AGENT_LOG` (§17.20.2) with the
**identical env-path / silent / graceful / feature-gated** contract, differing only in payload (full
content vs. compact metadata):

| Variable | Meaning | Default |
|---|---|---|
| `CRANELISP_AGENT_TRACE` | Path to the agent full-content **trace** file. **Set** ⇒ the agent appends the **full, untruncated** request/response transcript per exchange to this file. **Unset/empty** ⇒ **no trace is written** (the default). | — (unset = off) [S90] |

- **Path-only; the stderr sink is REMOVED.** `CRANELISP_AGENT_TRACE` no longer produces an
  ephemeral stderr view — there is **no `eprintln!` trace** any more. It is **set to a path** (a file
  sink) or it is off. A bare/legacy `=1`-style toggle is **not** a path and writes **no** trace
  (treated as off). This deliberately changes the variable's meaning from "stderr debug view" to
  "persistent full-content file", matching the `CRANELISP_AGENT_LOG` shape. [S90]
- **Silent — nothing extra in the REPL.** Exactly as §17.20.1: writing the trace produces **no**
  banner, no "tracing to …" line, no per-exchange echo, no transcript change. The session is
  **byte-identical** to the same session with tracing off. The trace is a **dev-session artifact**
  (NG4) — written off to the side, never surfaced, never in a `--link`/`--release` artifact. [S90]
- **Append, persistent, across turns and the session.** When set, each exchange **appends** to the
  file; it is the durable content record across the whole session (the old stderr view kept nothing). [S90]
- **Feature-gated; absent on the default build.** Like `CRANELISP_AGENT_LOG` and the whole agent, the
  trace exists **only** in an `--features agent` build; on a default build the variable is inert and
  **no trace is ever written** (feature-OFF stays byte-identical, §17.9). [S90]
- **Graceful on an unwritable path.** Exactly as §17.20.2: an unwritable `CRANELISP_AGENT_TRACE` path
  MUST **degrade silently** — never crash the session, never spew errors into the REPL. The trace is a
  side channel; its failure never disturbs the session. [S90]

#### 17.21.2 The Payload — Full, Untruncated Request/Response Transcript [S90]

Where the log records *that* an exchange happened (§17.20.3), the trace records its **full content**.
Per exchange it appends, **untruncated** (no ~80-char cap):

- the **assembled request** — the message turns sent to the model: each turn's **role** and, within
  it, the **block kinds** (system/context/primer/harvest, the user ask, prior tool results, etc.) and
  their **content** — the actual text, not a length-elided preview; and
- the **model's response** — the response **prose** and any **tool calls** it issued (pull requests,
  Build form-submits, Document edits), with their arguments.

The **content grain** of each block is owned by `/dev` (it consumes what the rig already assembles and
what the provider returns); this section pins the **experience requirement**: what reaches the file is
the **full** request/response — enough to re-read *exactly* what the agent was shown and what it
returned for the turn a §17.20 log line points at — with **nothing truncated**. [S90]

#### 17.21.3 The Shared `turn` Correlation Key — Joining Index to Content [S90]

The two sinks are **joined by a shared `turn` key** — a per-turn/exchange index, monotonic within a
session, stamped identically in both:

- the **§17.20 log** JSONL gains a **`turn`** field on every line (§17.20.3), and
- the **trace** emits a **matching per-turn marker** delimiting each exchange in the file (e.g. a
  `--- turn N ---`-style boundary carrying the same index; the exact marker text is `/dev`-owned),

so the **workflow** is: **grep the log** for a `repair`/`give_up`/struggle signal, read its `turn`,
then **scroll the trace** to that same `turn` marker to read the **full request and response** that
produced it. The `turn` index is the only coupling required between the sinks — each remains
independently writable (one may be set without the other), but when **both** are set they share the
index so the index→content join is mechanical. [S90]

## 18. Redefinition Semantics — Dependent Recompilation, Broken Symbols, and the Frozen World [S102]

Redefining a symbol in a live session is not always a local act: callers were compiled against the
old definition's **signature** — its type scheme today, and, once ownership modes ship, every other
ABI-bearing component of its compiled calling convention. This section specifies what the user
observes when a redefinition invalidates those compiled assumptions: which callers are recompiled,
how the turn reports it, what a symbol that can no longer compile looks like, and which world —
old or new — every route into the code sees afterwards.

Design references (non-normative): `design/arch/ownership-inference.md` §5.2–§5.7 (the
dependent-recompilation subsystem), `design/backend/ownership-codegen.md` §8 (trap stubs, slot
versioning). This section is the **normative user-facing contract**; the design docs describe
mechanism.

### 18.1 Two Classes of Redefinition [S102]

Every successful redefinition of an existing symbol is classified by the compiler into exactly one
of two classes. The classification itself is internal, but the observable split is normative:

- **Signature-preserving (ABI-preserving, "body-only")** — the redefinition leaves the symbol's
  compiled signature unchanged: same type scheme and, from increment I, same ABI-bearing
  ownership-mode surface. Body edits and docstring edits are the common case.
- **Signature-changing (ABI-changing)** — the redefinition changes any part of that surface.

The wording "signature-changing" is deliberately cause-agnostic: today the only signature-changing
cause is a type-scheme change; ownership-mode changes join the same class when they ship. All
requirements in this section apply uniformly to both causes.

**The coherence guarantee.** After any redefinition, a caller compiled against the old signature
MUST NOT reach the new body uncorrected. A signature-changing redefinition MUST leave every
compiled caller in one of exactly three states: **recompiled** against the new signature (§18.3),
**broken** — marked and trapped, never silently wrong (§18.4–§18.5) — or **frozen** on the old,
internally-consistent chain (closure values only, §18.7). Silent unsoundness (an old-signature
caller invoking a new-signature body) MUST NOT occur. [S101]

> **Scope note (S101 stage-M; T1 cure landed S103).** The coherence guarantee's MUSTs are
> delivered by **two mechanisms**, keyed on the redefinition **target**:
>
> 1. **Concrete single-signature function definition** (a plain `defn` with one monomorphic
>    signature) — the §18.3 **dependent-recompilation transaction**: affected callers are
>    recompiled (or marked broken and trapped) and the turn prints the `recompiled:`/`broken:`
>    cascade sections.
> 2. **Every other (downgrade / reuse-and-patch) target kind** — generic/constrained function,
>    overloaded function, macro, type/constructor, trait declaration or impl — the S103 **T1
>    full cure**: an **end-of-turn module reload** recompiles every compiled caller that would
>    otherwise be left on the previous definition, so the caller picks up the new definition
>    at re-entry and the §18.1.1 `stale:` section renders **empty**. On the two edge paths
>    where the reload cannot recompile the callers cleanly the split world is **surfaced, never
>    silently answered**: a reload failure (a caller left genuinely ill-typed by the new
>    definition — e.g. a concrete→overloaded downgrade that makes an unannotated caller
>    ambiguous) degrades the turn to the §14.4 error-blocked state; a regen-suppressed target
>    module (read-only backing file) keeps the interim `stale:` print. See
>    `design/int/session-transaction.md` §10 T1 (mechanics, CS-1/2/3) and the acceptance pair
>    `tests/repl_redefinition.rs::t1_full_cure_recompiles_stale_callers_stale_section_empty`
>    (positive — recompiled caller, empty section) / `t1_full_cure_body_only_edit_still_no_report_no_recompile`
>    (over-trigger guard — a body-only edit MUST NOT reload). The former coherent-stale pins
>    `redefine_concrete_to_polymorphic_caller_survives_coherent_stale` /
>    `redefine_concrete_to_overloaded_caller_survives_coherent_stale` **flipped** to the cured
>    behaviour (recompiled value / error-blocked-and-surfaced, no old-chain answer).
>
> **Still-uncured T1 residue (confirmation-level, FIXME 0533).** The T1 trigger is gated on a
> **slot change** (`new_slot.is_none() || old_slot.is_none()`), so a **slotted→slotted**
> redefinition — both the old and new target keep a live GOT slot — is excluded from the
> reload on the rationale that a reused slot late-binds correctly. The one edge that rationale
> does not cover is a `deftype` **constructor arity change** (`Point [x]` → `Point [x y]`): it
> is slotted→slotted, so it is excluded, yet it late-binds to an **incompatible arity** — a
> residual silent split-world with no report. This is a rare, design-acknowledged residue (not
> a shipped-defect regression), pending `/design`'s confirm-or-cure ruling. Requirements
> throughout §18.2–§18.8 are written against the full guarantee; this narrow slotted→slotted
> arity case is the only remaining gap.

#### 18.1.1 The Downgrade Report — a Split World Is Never Silent [Tested+Neg tests/repl_redefinition.rs::t1_full_cure_recompiles_stale_callers_stale_section_empty, tests/repl_redefinition.rs::t1_full_cure_body_only_edit_still_no_report_no_recompile]

When a redefinition takes the reuse-and-patch downgrade path (a non-concrete target — the
at-scale default for unannotated, generalizing functions), the end-of-turn module reload
(§18.1 scope note; `design/int/session-transaction.md` §10 T1) **recompiles** every compiled
caller that would otherwise be left on the previous definition. The negative-MUST — the
silent outcome, old behaviour continuing behind a fresh confirmation line with no
indication — is satisfied **by construction**: no caller is left stale, so there is nothing
to report and the `stale:` section renders **empty**. [S103]

The `stale:` section is a section of that same end-of-turn transaction report — the same
`TransactionReport` channel as §18.3's `recompiled:`/`broken:` sections, in the same
comment-line layout family, rendered empty on the normal (successful-cure) path and printed
with a non-empty set only on the two edge paths where the reload cannot recompile the callers
cleanly (below). Its header + name-line format when it does print:

```
:{NewType} {module}/{name} ; defn
; stale: compiled callers keep the previous definition of {module}/{name}
;  {name} {name} ...
```

- **The section header line is exact**: `; stale: compiled callers keep the previous
  definition of {cause}`, where `{cause}` is the fully-qualified name of the redefined
  symbol. [S102]
- **The name lines** use the related-symbols layout of §1.1 (the §3.3 L0–L4 layout
  algorithm), exactly as §18.3's sections: callers in the current module appear bare;
  callers in other modules appear module-qualified. [S102]
- **The set MUST be exact both ways** (on an edge path, where it prints): it MUST name every
  compiled caller the reload could **not** recompile against the new definition, and MUST NOT
  name any symbol that picks up the new definition — recompiled callers, late-bound callers,
  and never-compiled callers do not appear. [S103]
- **The section is empty on the normal (successful-cure) path** — when the end-of-turn reload
  recompiles the stale callers, the turn prints only the §1.3 confirmation (silently — no
  `recompiled:` line either), exactly like a body-only edit (§18.2). A body-only edit itself
  never triggers a reload (the over-trigger guard). The report exists to surface a split world
  the reload could not close, not to annotate every redefinition. [S103]
- **The section prints only on the two reload-edge paths, and always surfaces the split
  world — never a silent answer.** It carries a non-empty `stale:` set only when the reload
  cannot recompile the callers cleanly: (a) a **reload failure** — the recompiled caller no
  longer type-checks against the new definition (e.g. a concrete→overloaded downgrade that
  leaves an unannotated caller genuinely ambiguous) — degrades the turn to the §14.4
  error-blocked state (never a lockout or a silent old-chain answer) and keeps the `stale:`
  print; and (b) a **regen-suppressed** target module (read-only backing file — the
  `should_regenerate` guard) keeps the interim `stale:` print, because reloading would read
  stale disk source. On both edge paths the named callers keep running the old,
  internally-consistent chain until the block is lifted or the file is made writable. [S103]

Worked example — `id`'s prior definition is generic, so its redefinition takes the
reuse-and-patch downgrade path; `g` was compiled against the old `id`. The end-of-turn
reload recompiles `g` against the new `id`, so no `stale:` section prints and `(g 1)` sees
the new definition:

```
user> (defn id [x] x)
:(Fn [a] a) user/id ; defn

user> (defn g [x] (id (+ x 1)))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (g 1)
:primitives/Int 2

user> (defn id [x] (+ x 100))       ; g is recompiled silently — no stale, no recompiled: line
:(Fn [primitives/Int] primitives/Int) user/id ; defn

user> (g 1)                          ; recompiled against the new id
:primitives/Int 102
```

The redefinition turn prints only its §1.3 confirmation — the recompile is **silent** (no
`; stale:` section and no `; recompiled:` line): the cure leaves nothing stale to report.

> **The Principle-8 shape (non-normative).** The end-of-turn module reload
> (`design/int/session-transaction.md` §10 T1) recompiles exactly the callers a pre-cure
> `stale:` set would have named, so the set is empty and the section does not print on the
> normal path. The `stale:` section is therefore a section of the same transaction report the
> reload keeps (rendered empty), not throwaway output — the Principle-8 shape the S102
> architecture review pinned. It re-appears only on the reload-edge paths (a reload failure or
> a regen-suppressed module), where it names the callers the reload could not recompile.

| Requirement | Test |
|---|---|
| A type-changing redefinition with a compiled caller either recompiles the caller or marks it broken — the caller MUST NOT reach the new body uncorrected | [Tested+Neg tests/repl_redefinition.rs::type_change_redefinition_compiled_caller_never_reaches_new_body_uncorrected, tests/repl_redefinition.rs::type_change_redefinition_polymorphic_caller_recompiles_and_works] (concrete single-sig UserFn targets via §18.3; T1-kind targets via the S103 end-of-turn reload cure — tests/repl_redefinition.rs::redefine_concrete_to_polymorphic_caller_survives_coherent_stale and tests/repl_redefinition.rs::redefine_concrete_to_overloaded_caller_survives_coherent_stale flipped to the cured behaviour) |
| A downgraded (reuse-and-patch) redefinition recompiles its stale compiled callers at end-of-turn, so the §18.1.1 `stale:` section renders **empty** and a previously-stale caller sees the new definition at re-entry | [Tested+Neg tests/repl_redefinition.rs::t1_full_cure_recompiles_stale_callers_stale_section_empty, tests/repl_redefinition.rs::t1_downgrade_report_names_stale_compiled_callers_exactly] |
| A body-only edit MUST NOT trigger the reload — it prints only the §1.3 confirmation, no `stale:`/`recompiled:`/`broken:` section (over-trigger guard) | [Tested+Neg tests/repl_redefinition.rs::t1_full_cure_body_only_edit_still_no_report_no_recompile, tests/repl_redefinition.rs::t1_downgrade_report_neg_body_only_turn_prints_no_stale_section] |
| A downgraded redefinition with no compiled caller left behind prints only the §1.3 confirmation — no `stale:` section | [Tested tests/repl_redefinition.rs::t1_downgrade_report_neg_omitted_when_no_compiled_caller] |
| On a reload-edge path the split world is surfaced, never silently answered: a reload failure degrades to §14.4 error-blocked (liftable by repair), keeping the `stale:` print | [Tested tests/repl_redefinition.rs::t1_reload_failure_error_block_lifts_on_caller_repair, tests/repl_redefinition.rs::redefine_concrete_to_overloaded_caller_survives_coherent_stale] |

### 18.2 Signature-Preserving Redefinition — Late Binding Preserved [Tested]

A signature-preserving redefinition behaves exactly as today, and this section pins that behaviour
against regression:

- The turn's output is the ordinary definition confirmation (§1.3) and nothing else. No dependent
  recompilation is performed and **no cascade report is printed** (§18.3) — body-only edits MUST
  NOT produce cascade noise. [S101]
- **Late binding is preserved.** Every existing route into the symbol — direct callers, closure
  values minted before the edit, curried partials, in-flight computations — picks up the new body
  at its next call. This is the prized REPL semantic for body edits and it MUST be retained. [S101]
- **Cost is a single-symbol compile.** The turn MUST remain at today's cost — typecheck + codegen
  of the redefined symbol only, with no per-dependent work. [S101]

```
user> (defn f [x] (+ x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (defn f [x] (+ x 10))        ; body-only: same signature
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (g 1)
:primitives/Int 11
```

| Requirement | Test |
|---|---|
| body-only redefinition prints only the §1.3 confirmation — no cascade sections | [Tested+Neg tests/repl_redefinition.rs::redefine_body_only_neg_no_cascade_report_no_dependent_recompiles] |
| existing closure values pick up the new body at their next call | [Tested+Neg tests/repl_redefinition.rs::redefine_body_only_stale_closure_late_binds_new_body] |
| body-only redefinition turn stays at today's single-symbol cost | [Tested tests/perf/l_d1_turn_latency.py (gate-time perf lane, not in canonical nextest; S101 Wave-5 record: median 0.0ms both polarities, tests/plan/ledger.md); slot-churn negative: tests/repl_persist_redefine.rs::persist_body_only_redefinition_neg_keeps_slot] |

### 18.3 Signature-Changing Redefinition — The Cascade Report [S101]

A signature-changing redefinition triggers **dependent recompilation**: the session re-typechecks
and recompiles the affected callers (transitively, callees before callers). The turn's output
reports the outcome so the user knows exactly which world every symbol is in.

The turn prints the ordinary definition confirmation (§1.3) for the redefined symbol, followed by
up to two comment-line sections in this order:

```
:{NewType} {module}/{name} ; defn - {docstring}
; recompiled:
;  {name} {name} ...
; broken:
;  {name} — {original error}
```

- **`recompiled:`** names the symbols the transaction re-typechecked and recompiled successfully.
  The section uses the related-symbols layout of §1.1 (the §3.3 L0–L4 layout algorithm): symbols
  in the current module appear bare; dependents in other modules appear module-qualified. The set
  MUST be exact — it MUST name every symbol recompiled by the transaction and MUST NOT name any
  symbol that was not (unaffected functions never appear). [S101]
- **`broken:`** names the symbols that no longer typecheck under the new signature, one line per
  symbol: the name, an em-dash, and the error that broke it (category + location + message per
  §5.1, types fully qualified per §5.3; the location span is within the broken symbol's source).
  The reason SHOULD fit on one line; the full error remains readable via `/info` (§18.4). [S101]
- Either section is **omitted entirely when empty**. A signature-changing redefinition with no
  compiled dependents prints only the §1.3 confirmation, exactly like a body-only edit. [S101]

Worked example — `g` survives the change (its own signature updates in turn), `k` does not:

```
user> (defn f [x] (+ x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (defn k [x] (f (* x 2)))
:(Fn [primitives/Int] primitives/Int) user/k ; defn

user> (defn f [s] (primitives/str-len s))   ; signature change: Int -> Int becomes String -> Int
:(Fn [primitives/String] primitives/Int) user/f ; defn
; recompiled:
;  g
; broken:
;  k — type error at 12..23: type mismatch: expected primitives/String, got primitives/Int
```

`g`'s body still typechecks (`x` flows through unconstrained), so `g` is recompiled — and its own
signature is now `(Fn [primitives/String] primitives/Int)`; if `g` had compiled callers they would
join the transaction in turn and appear in the same `recompiled:`/`broken:` sections. `k`'s body
pins its argument to `Int`, so `k` cannot be recompiled: it is marked **broken** (§18.4).

**Errors are reported, never hidden — and never block the session.** A broken dependent is
ordinary session state, not a module-level error: evaluation of everything else continues, and the
§14.4 error-blocking mechanism (which governs whole-module recompile failures from external file
edits) MUST NOT be triggered by symbol-level breaks. Only calls that actually reach a broken
symbol fail — loudly, per §18.5. [S101]

| Requirement | Test |
|---|---|
| recompiled set names exactly the recompiled callers, positive and negative | [Tested+Neg tests/repl_redefinition.rs::redefine_abi_change_cascade_report_names_exact_affected_set] |
| broken set names each broken symbol with its §5.1-format reason | [Tested tests/repl_redefinition.rs::redefine_abi_change_cascade_report_names_exact_affected_set] |
| empty sections are omitted | [Tested tests/repl_redefinition.rs::redefine_recovery_reverting_callee_recompiles_caller (broken: omitted on the all-green revert turn); Gap(S101): the signature-changing-with-zero-dependents shape is not directly pinned] |
| symbol-level breaks do not block unrelated evaluation | [Tested tests/repl_redefinition.rs::redefine_abi_change_cascade_report_names_exact_affected_set (recompiled caller runs while its sibling is broken)] |

### 18.4 Broken Symbols — Status and Provenance Introspection [S101]

A symbol that failed re-typechecking during a cascade is **broken**. Its definition metadata —
last-good signature, docstring, source — remains intact and introspectable; only its compiled code
is gone. Broken-ness is ordinary, recoverable session state (§18.6), not a sticky mode.

**The provenance phrase.** Everywhere broken status is displayed, provenance uses one normative
phrase:

```
broken by the redefinition of {cause}: {original error}
```

where `{cause}` is the fully-qualified name of the redefined symbol that broke this one, and
`{original error}` is the §5.1-format error (category + message, types fully qualified) produced
when re-typechecking failed. [S101]

**Bare lookup is self-documenting.** A broken symbol entered bare at the prompt MUST respond with
what it is and why it is broken — never an opaque error (root `CLAUDE.md` §Design Principles). The
display is the symbol's ordinary per-class §4.1 display — the type shown is the **last successfully
compiled signature** — plus one comment line carrying the provenance phrase: [S101]

```
user> k
:(Fn [primitives/Int] primitives/Int) user/k ; defn
; broken by the redefinition of user/f: type error at 12..23: type mismatch: expected primitives/String, got primitives/Int
```

**`/sig` on a broken symbol** MUST show the same primary line and provenance comment line as bare
lookup. [S101]

**`/info` on a broken symbol** MUST include the primary line, the provenance comment line, and the
definition source (per §3.6). It MUST NOT display code size or compile-time statistics for a broken
symbol — there is no compiled code, and the trap stub is an implementation detail that MUST NOT be
presented as the symbol's code. [S101]

```
user> /info k
:(Fn [primitives/Int] primitives/Int) user/k ; defn
; broken by the redefinition of user/f: type error at 12..23: type mismatch: expected primitives/String, got primitives/Int
  (defn k [x] (f (* x 2)))
```

**Provenance is depth-1.** `{cause}` names the redefinition that directly broke the symbol. Callers
of a broken symbol are NOT themselves marked broken — their compiled code is still valid (the
broken symbol's signature did not change; it failed before producing a new one) — they simply reach
the trap through the broken symbol at runtime (§18.5). [S101]

| Requirement | Test |
|---|---|
| bare lookup of a broken symbol shows per-class display + provenance line, no opaque error | [Gap(S101): bare-lookup leg not directly pinned — the rendering is the same shared `broken_status_line` seam `/sig` exercises (design/int/session-transaction.md §9.2), covered there] |
| `/sig` shows broken status + provenance | [Tested+Neg tests/repl_redefinition.rs::redefine_broken_caller_info_and_sig_report_broken_status] |
| `/info` shows broken status + provenance + source, no code-size/compile-time stats | [Tested+Neg tests/repl_redefinition.rs::redefine_broken_caller_info_and_sig_report_broken_status] |
| callers of a broken symbol are not marked broken | [Gap(S101): depth-1 provenance not directly pinned e2e; the trap lanes exercise unrecompiled callers reaching the trap without themselves breaking] |

### 18.5 The Trap — Calling a Broken Symbol [S102]

Any call that reaches a broken symbol at runtime MUST raise a clean runtime error — the **trap** —
presented through the standard runtime-error format (§5.1, `runtime error: ` category prefix) with
the trap message:

```
{broken} is broken by the redefinition of {cause}: {original error}
```

where `{broken}` and `{cause}` are fully-qualified symbol names and `{original error}` is the same
embedded error as §18.4's provenance phrase. As seen at the prompt: [S101]

```
user> (k 3)
runtime error: user/k is broken by the redefinition of user/f: type error at 12..23: type mismatch: expected primitives/String, got primitives/Int
```

- **The presentation is exact.** The `runtime error: ` category prefix is followed directly
  by the trap message, exactly as the transcript above shows. The trap line carries no
  location span of its own — a runtime trap has no meaningful source location, and §5.1's
  location requirement is satisfied by the location inside `{original error}`. No internal
  wrapper text (e.g. an `Error:` / `codegen error at 0..0:` / `runtime panic:` chain) may
  appear before, between, or around the category prefix and the trap message. [S102]
- **Every route traps.** The trap MUST be reached by every call path into the broken symbol:
  direct by-name calls, calls from compiled (unrecompiled) callers, closure values minted from the
  symbol **before** the break, and curried partials of it — regardless of when the value was
  created. [S101]
- **Trapping is a deliberate ruling, not a necessity.** The broken symbol's stale code would be
  memory-safe to serve (it is internally consistent with the frozen old chain, §18.7) — but
  silently executing code that diverges from the source the user just changed is the worse
  experience. A broken symbol MUST fail loud, with provenance, recoverably; it MUST NOT serve its
  stale behaviour. [S101]
- **The session survives.** A trap is an ordinary runtime error under §5: the REPL prints it,
  recovers per §5.2, and all other definitions remain callable. Repeated trap invocations MUST NOT
  crash or corrupt the session. [S101]
- **Bounded leak note.** A trap fires after the caller has already prepared the call's arguments;
  the raise path does not release them. One bounded reference leak per trap invocation is
  permitted — the same caveat class as every runtime panic — and is reclaimed at session end.
  Heap-balance checks around traps assert boundedness, not zero. [S101]

| Requirement | Test |
|---|---|
| direct call of a broken symbol raises the trap message with provenance | [Tested+Neg tests/repl_redefinition.rs::redefine_abi_change_broken_caller_direct_call_traps_with_provenance] |
| trap presentation is exact: `runtime error: ` + trap message — no synthetic span, no wrapper chain | [S102 — guard tests/repl_redefinition.rs::trap_presented_in_normative_runtime_error_format, failing-not-ignored until the /int fix] |
| a closure value minted before the break reaches the trap | [Tested tests/repl_redefinition.rs::redefine_broken_caller_value_use_wrapper_minted_before_break_reaches_trap (closest-reachable stage-M carrier — see the test-file header residue note)] |
| a curried partial minted before the break reaches the trap | [Tested+Neg tests/repl_redefinition.rs::redefine_broken_caller_curried_partial_reaches_trap] |
| repeated traps neither crash nor corrupt; leak is bounded per invocation | [Tested tests/repl_redefinition.rs::redefine_trap_invocations_leak_bounded_per_trap] |

### 18.6 Recovery — Both Directions [Tested+Neg]

Broken-ness is repaired **by redefinition**, in either direction; each redefinition re-runs the
same transaction:

- **Fix the broken symbol**: redefine it to match the new signature. It re-typechecks, recompiles,
  and is green — the turn prints the ordinary §1.3 confirmation (plus its own cascade sections if
  *its* signature changed for its callers). [S101]
- **Fix the cause**: redefine the causing symbol back to a signature under which the broken symbol
  typechecks. The broken symbol is a static caller, so it rejoins the transaction, recompiles, and
  appears in the turn's `recompiled:` section. [S101]

```
user> (defn f [x] (+ x 1))          ; put f back
:(Fn [primitives/Int] primitives/Int) user/f ; defn
; recompiled:
;  g k
```

After recovery the symbol MUST be indistinguishable from one that was never broken: calls succeed,
and bare lookup, `/sig`, and `/info` MUST NOT show any broken/provenance line. [S101]

| Requirement | Test |
|---|---|
| redefining the broken symbol to match ⇒ green, callable, no provenance residue | [Tested+Neg tests/repl_redefinition.rs::redefine_recovery_fixing_caller_clears_broken] |
| redefining the cause back ⇒ broken symbol recompiles and appears in `recompiled:` | [Tested+Neg tests/repl_redefinition.rs::redefine_recovery_reverting_callee_recompiles_caller] |

### 18.7 Frozen-World vs Late-Binding — Which World a Value Sees [S101]

The two redefinition classes give two deliberately different semantics for values that already
exist when the redefinition lands:

- **Signature-preserving ⇒ late binding (today's semantic, §18.2).** Every existing value and
  caller sees the new body at its next call.
- **Signature-changing ⇒ frozen world for pre-break closure values.** Recompilation can reach
  everything callable **by name**, but not closure values already on the heap — they embed direct
  code pointers. Rather than allow a mixed-signature call (unsound) or invalidate live values
  (stop-the-world), the old code chain is **frozen**: a closure value minted before a
  signature-changing redefinition, invoked after it, MUST see the **old chain's behaviour,
  transitively** — its calls resolve to the pre-redefinition definitions all the way down,
  consistently. It MUST NOT crash, MUST NOT corrupt memory, and MUST NOT observe a mix of old and
  new signatures, including under sustained repeated invocation. [S101]
- **By-name calls always see the current world.** Recompiled callers and every call made by name
  after the turn MUST see the new definitions (or trap, if broken). The cascade report (§18.3) is
  where the user sees which world each *symbol* is in; frozen behaviour is reachable only through
  *values* minted before the break. [S101]

Worked example — the contract for any pre-break closure value still live at the break (held in a
container, captured by a suspended computation, or pinned by an in-flight strand):

```
user> (defn f [x] (+ x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

;; a closure value over g is minted here and stays live on the heap:
;;   stale = (fn [x] (g x))          — compiled against g's Int -> Int chain

user> (defn f [s] (primitives/str-len s))   ; signature change
:(Fn [primitives/String] primitives/Int) user/f ; defn
; recompiled:
;  g

user> (g "hello")                    ; by name: the new world
:primitives/Int 5

;; (stale 5) — the pre-break closure: the frozen old chain, transitively
;; => 6   (old g -> old f: 5 + 1), not a type error, not a crash
```

The frozen world is a **session-memory commitment only**: frozen chains die with the session, and
a restart rebuilds everything from source in the current world (§18.8).

| Requirement | Test |
|---|---|
| pre-break closure invoked after a signature change sees old-chain behaviour transitively | [Gap(S101): no cross-turn value carrier is REPL-reachable at stage M (qa plan §6.1.1 addendum); structural witness: tests/repl_persist_redefine.rs::persist_abi_change_allocates_fresh_slot_hole_survives_restart — add the direct test when a carrier ships] |
| sustained invocation of a stale closure: no crash, no mixed-signature corruption | [Tested tests/repl_redefinition.rs::redefine_abi_change_closure_minting_caller_rejoins_new_world_coherently (400-invocation sustained leg)] |
| by-name calls and recompiled callers see the new definitions | [Tested+Neg tests/repl_redefinition.rs::redefine_abi_change_closure_minting_caller_rejoins_new_world_coherently] |

### 18.8 Interaction with Session Persistence [S101]

Redefinition persistence follows §15: the backing file always reflects the latest source of every
definition (§15.6), including definitions that are currently broken — the broken symbol's *source*
is unchanged and still the user's authored truth. Broken-ness itself is session state, not
persisted state: it is never written to disk as a trap, and is re-derived from source at restart.
Consequences:

- After a signature-changing redefinition that leaves symbols broken, the regenerated backing file
  taken as a whole does not typecheck. On session restore (§15.2), the session MUST NOT silently
  serve stale compiled code for those symbols and MUST NOT silently drop them. The normative floor
  is **reconstruction as a load-time compile error**: the backing file is recompiled from source
  through the standard load-error path, and the broken definition MUST surface as an ordinary
  compile error naming the broken symbol and carrying the underlying type error. [S101] [Gap(S101): the broken-then-restart floor is not directly pinned e2e; the L-R5 lanes (tests/repl_persist_redefine.rs) assert the floor's substrate — complete metas, no stale-slot serve — per the S101 Phase-3 gate note 3]
- **The restart MUST reach a prompt.** A backing file that fails to recompile at restore MUST
  NOT prevent the REPL from starting: broken-ness is ordinary, recoverable session state
  (§18.4), and the primary repair path is redefinition at the prompt (§18.6) — a startup that
  exits on the load error locks the user out of exactly that repair path, leaving hand-editing
  the backing file as the only recovery. Instead the session MUST start, display the load error
  (per §5.1, naming the broken symbol), and enter the §14.4 error-blocked state for the failing
  module: slash commands remain available, evaluation is refused with the §14.4 message, and the
  error clears when a subsequent definition turn (or an external file fix, §14.6) makes the
  module compile — at which point the session proceeds normally. [S102] (As-built at S101 the
  REPL exits with code 1 before the first prompt — see FIXME 0489.)
- To guarantee that floor, a compiled-cache snapshot (`.o`/`.meta`) MUST NOT be written for a
  module that holds a broken symbol at write time — a cache MUST never capture a trap stub as the
  module's compiled truth, so no restart can serve stale code for a broken definition. Skipped
  writes self-heal: the first fully-green turn persists normally. [S101] [Gap(S101): poisoning implemented at src/session_v4/nice_worker.rs (broken-module persist gate, verified live at Wave 4) — no direct e2e pin yet]
- This qualifies §15.4's round-trip invariant for the broken-session case: symbol-grain broken
  state (status + provenance, §18.4) degrades at restart to a load-grain compile error. Restoring
  broken symbols *as broken, with the same provenance* — so the §15.4 round-trip reproduces the
  full session state, broken-ness included — is a **non-normative future target** (MAY), not
  asserted by the current test lanes; any implementation of it MUST still satisfy the floor above
  (same errors surfaced, no stale code, no silent drop). [S101]
- Definitions recompiled or redefined across signature changes MUST restore correctly from a valid
  cache after restart — a program that ran before `/quit` runs identically after. [Tested tests/repl_persist_redefine.rs::persist_abi_change_redefinition_restart_runs_correctly_from_cache]
