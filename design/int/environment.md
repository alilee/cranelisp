# Process environment: file supply and linked parameters

Owner: `design` (int). Subordinate to [the master](int.md). Status: designed
in S123 Phase 3 to the user's rulings of 2026-11-15; not implemented.

This document covers how the compiler process gets its environment before
anything reads it, and how a `--link` executable carries its runtime switches.

- Requirements: [CLI §0.8](../../repl/spec/00-cli-invocation.md#08-environment-files-and-linked-parameters)
  and [§0.7](../../repl/spec/00-cli-invocation.md#07-execution-environment-variables-s93).
  The decision source is the S123 Phase 3 user rulings in `sprints/SPRINT.md`.
- Architecture: [process-ending panics and the environment supply](../arch/s123-panics-and-environment.md)
  §2, the contract this interior realises. The runtime's switch source, its
  capture format and its install entry are intrinsics'
  ([process lifecycle §2](../intrinsics/process-lifecycle.md#2-runtime-switches)).

## 1. Shape

- **One supplier, then the process environment alone.** The binary reads the
  files once at startup and copies each admitted key that the process
  environment does not already define into the process environment. After
  that, every reader in every crate keeps reading `std::env` as it does
  today. No library crate reads a configuration file, and no typed
  configuration value is passed between crates
  ([Principle 07](../arch/principles/07-single-source-of-truth.md),
  [Principle 02](../arch/principles/02-narrow-interfaces.md)).
- **Home.** One binary-private module, proposed `src/env_files.rs`. It holds the
  admission predicate, the parser, file location, precedence and the one
  `set_var` loop. `main.rs` calls it once.
- **Repeated reads stay as written.** Nothing writes the environment after
  the supply, so a switch read on every call already returns its startup
  value. Moving any reader to a startup value is optional hygiene owned by
  that reader's crate (arch §2.1).
- **The binary never names a runtime switch.** Linking embeds an opaque
  capture that intrinsics produces and decodes (§3).

## 2. The supply

### 2.1 Ordering

The first statements of `main` become:

1. `parse_args`: pure. It resolves the project root and may exit with a usage
   error. It must not read the environment or start a thread.
2. **The supply** (§2.2), given the resolved project root. A supply error
   (§2.5) prints its located message to stderr and exits 1.
3. Everything that reads the environment or starts a thread, in its current
   order: the trace and panic-hook installers, `install_if_enabled`, the
   `CRANELISP_RC_STATS` arm, `init_color`, the exit-time trace flush
   ([observability §7.1](observability.md#71-process-exit-and-panic-wiring)),
   then `run`.

Today step 3 runs before `parse_args`; it moves after the supply. Under
edition 2024 `set_var` is `unsafe` and is sound only while no other thread
exists. The order above gives that structurally: `sched_dump` and the
workers start inside step 3 or later.

- Grade: asserted, with a named falsifier. Falsifier: a thread spawn or an
  environment read reachable from `parse_args` or from the supply itself.
- Usage errors and supply errors print before `init_color`, so they are
  uncoloured, as usage errors are today.

### 2.2 Algorithm

1. Read the loader controls from the process environment only (§2.4). If the
   disable control is set, stop.
2. Locate the project file and the user file (§2.3). A missing file is
   silently absent.
3. Read and parse each present file into ordered `(key, value, line)` entries
   (§2.5). An unreadable or malformed file stops startup.
4. Keep only admitted keys (§2.6). For each, if the process environment
   defines it (even as an empty value), keep that. Otherwise take the project
   file's value, else the user file's. Within one file, the last occurrence
   wins.
5. Set each chosen value with one `set_var` loop.

Children inherit the result. That includes the system linker under `--link`,
`/sh` and the test runner's child processes, which are started with the
loader disabled so their configuration is exactly the parent's
([test runner §6.5](test-runner.md#65-the-test-child)).

### 2.3 File locations

- **Project file:** `.env` in the resolved project root, which is
  `resolve_target_from`'s answer. In the default case that is the working
  directory.
- **User file:** `$XDG_CONFIG_HOME/cranelisp/env` when `XDG_CONFIG_HOME` is
  set and non-empty, else `$HOME/.config/cranelisp/env`. With neither set, there
  is no user file.

Both locations come from the process environment. `XDG_CONFIG_HOME` and `HOME`
are not admitted keys, so a file cannot move a file.

### 2.4 Loader controls

The controls come from the process environment only (CLI §0.8):

| Control | Effect |
|---|---|
| `CRANELISP_NO_ENV=1` | Read neither file. |
| `CRANELISP_ENV_FILE=<path>` | Read this path instead of the project `.env`. |
| `CRANELISP_USER_ENV_FILE=<path>` | Read this path instead of the user file. |

- The controls are `CRANELISP_`-prefixed but excluded from admission (§2.6),
  so a file line that sets one is ignored. A control's answer never depends
  on reading a file.
- An override path that does not exist is a missing file, so it is silent,
  like the default location.
- The suite must never inherit a developer's files. Which repository-level
  declaration sets `CRANELISP_NO_ENV` for it is `qa`'s choice, and it lands in
  the same change-set as the loader (arch §2.1). Loader tests clear it in the
  child environment.

### 2.5 Syntax, unreadable and malformed files

The ruling is dotenv syntax. This parser accepts the common dotenv core and
defines nothing beyond it:

- blank lines, and lines whose first non-blank character is `#`;
- `KEY=VALUE`, with an optional `export ` prefix. A key is ASCII letters,
  digits and `_`, and does not start with a digit. Whitespace around the key
  and `=` is ignored;
- an unquoted value runs to the end of the line, with trailing whitespace
  removed. A ` #` begins a comment;
- a single-quoted value is literal;
- a double-quoted value may span lines and understands the escapes `\n`,
  `\"` and `\\`;
- no interpolation. `${NAME}` is literal text.

Dialects differ on interpolation and inline comments. This set is the part
the common implementations agree on. Stating it as a user-facing contract is
`spec`'s (§5).

**A malformed file is a startup error, in every mode** (CLI §0.8). Malformed
means a line that is not blank, a comment or an assignment, an invalid key,
or an unterminated quote. This holds for every line, not only for admitted
keys, because the ruling is about the file. A `.env` shared with another tool
must therefore stay inside this syntax.

**An unreadable file is a startup error.** Unreadable means the file exists
but cannot be opened or read (permissions, a directory, invalid UTF-8).

Both errors name the file and, when malformed, the line. They never contain a
value (§2.7).

- No `dotenv` crate is used. The available crates expand variables and set the
  environment themselves. That would make their dialect our observable
  contract and bypass admission and precedence.

### 2.6 Admission

One predicate: the key starts with `CRANELISP_`, or it is one of `NO_COLOR`,
`ANTHROPIC_API_KEY` or `OLLAMA_API_BASE_URL`, and it is not a loader control
(§2.4). All other keys are ignored. The prefix rule covers undocumented
switches without a registry.

### 2.7 Protected data

- **Protected:** values, because `ANTHROPIC_API_KEY` and `CRANELISP_AGENT_KEY`
  are secrets.
- **Permitted in diagnostics:** the file path, the line number and the key
  name.
- Startup prints no list of loaded files and never names which file supplied
  a setting. The agent banner reports state, provider and model only
  ([agent §6.3](agent.md#63-provider-selection)).
- A project `.env` that selects a provider while the key comes from the shell
  is a user-accepted residual.

## 3. Linked executables: baked switches

- **Compile-only switches** (for example `CRANELISP_NO_LENIENT`,
  `CRANELISP_NO_OWNERSHIP`, `CRANELISP_CODEGEN_DUMP`) shape the emitted code
  at `--link` and need no payload.
- **Runtime switches** are intrinsics' closed member set. Int bakes whatever
  that set holds and keeps no list of its own (Principle 07). Agent variables
  are not members, so they cannot be baked; this is structural, not a filter.

### 3.1 Mechanism

- **Capture.** `link_by_name` calls intrinsics'
  `runtime_switches::capture_runtime_switches()` after the supply (§2). So a
  file-supplied value bakes exactly as a shell value does. The bytes are
  opaque: int never parses them and never names a switch.
- **Embed.** `exe::generate_startup_object` places the bytes in one read-only
  data object.
- **Install.** The startup stub's first call, before
  `cranelisp_init_primitives`, passes the object's address and length to
  `cranelisp_install_runtime_switches`. The stub always makes the call, even
  when nothing is set, so the linked runtime never reads its launch
  environment. The stub's sequence is `install → init → run → exit`
  ([io-integration §1.2](io-integration.md#12-a-runtime-panic-ends-the-process-the-host-side)).
- **Force-link.** `crates/cranelisp-exe-bundle` gains
  `pub use cranelisp_intrinsics::runtime_switches;` in the same change-set
  (packet row P8).
- **No environment mutation.** The stub does not copy baked values into the
  executable's environment, so platforms and child processes see the
  environment the program was started with (arch §2.2).
- **Worker count.** The linked program's worker pool uses the machine's core
  count. Intrinsics builds the pool at install
  ([process lifecycle §2.3](../intrinsics/process-lifecycle.md#23-the-worker-count)),
  so the stub needs nothing more.
- **In the compiler process** (`--run`, the REPL, `--test` and test
  children) nothing is installed. The runtime reads the process environment,
  which the supply has already populated.
- **Cache.** The capture lives only in the per-link startup object, which is
  never cached. Cache keys are unchanged. A linked executable therefore
  depends on the environment present at `--link`, which `docs` should state.

### 3.2 Assurance

- **Structural:** the binary handles only opaque bytes, and the stub calls the
  install unconditionally.
- **Measured:** `qa`'s cells (int §16.0, S123 bullet). A switch present at
  `--link` takes effect without being in the executable's environment. The
  negative leg: a switch present only in the executable's launch environment
  has no effect.
- **Detective, owned by intrinsics:** an install after the first read is a
  hard failure, so a read ahead of the install cannot silently use the wrong
  source.

## 4. Module evidence (`dev`)

Unit rows in the proposed `src/env_files.rs`, one per scenario class:

1. Admission: prefix keys and the three named keys are admitted; `PATH`,
   `LD_LIBRARY_PATH` and the three loader controls are not.
2. Precedence: process over project over user; empty process values still
   win; the last occurrence within a file wins.
3. Syntax: `export`, comments, blank lines, inline comments, both quote
   styles, a multi-line double-quoted value and its escapes, and `${X}` kept
   literal.
4. Malformed and unreadable: an unterminated quote, an invalid key and a
   non-assignment line, each on a foreign key as well as an admitted one, are
   located errors whose messages omit the value. A directory or invalid UTF-8
   at a file location is an unreadable error. A missing file, default or
   overridden, is silent.
5. Location: `XDG_CONFIG_HOME` over `HOME`; `CRANELISP_ENV_FILE` replaces only
   the project file and `CRANELISP_USER_ENV_FILE` only the user file;
   `CRANELISP_NO_ENV` reads neither.

The parser and resolution are pure functions over strings and an injected
environment view, so these rows set no process environment. Only the final
`set_var` loop touches the process, and it has no branches to test.

## 5. Left to the owning roles

- **The dialect.** CLI §0.8 says "dotenv syntax". §2.5 is the design's
  reading. Whether `spec` states the accepted set is `spec`'s question for the
  user. A wider dialect changes only the parser.

## 6. Potential extensions

- **Per-session reload of files.** Not designed. Trigger: a requirement that
  editing `.env` affects a running REPL.
- **Windows user-file location** (`%APPDATA%`). Trigger: a supported Windows
  host.
