# `Cranelisp.toml` project configuration

Int's design for reading `Cranelisp.toml`, assembling the library and platform
directory sets, and scaffolding a default file. The normative contract is
`spec/08-modules.md` §8.11.1–§8.11.5 and `repl/spec/00-cli-invocation.md`
§0.5.7. Project-root derivation is [project-root resolution](repl-lifecycle.md#6-project-root-resolution).
The implementation is `src/session_setup.rs`.

## 1. Location and schema

- **Location.** The file is only ever `{project_root}/Cranelisp.toml`; no
  search walks up to parent directories.
- **Schema.** The private `ProjectConfig` has two optional keys, both lists of
  paths that default to empty:
  - `lib-dirs` (§8.11.4);
  - `platform-dirs` (§8.11.5).

  Unknown keys are ignored.
- **Paths.** A relative path is joined onto the project root. An absolute path
  is used unchanged. There is no tilde expansion.
- **Loaders.** `load_project_config_lib_dirs` and
  `load_project_config_platform_dirs` each return:
  - `Ok(None)` for an absent file;
  - `Ok(Some(dirs))` for a parsed file, possibly with an empty list;
  - a `ModuleError` naming the file and the parse or read error, and citing
    the spec clause, for an unreadable or malformed file.

## 2. Directory assembly

Every source only adds directories, so an absent, empty or keyless file removes
nothing (§8.11.4, the additive union).

| Set | Function | Order (first match wins) |
|---|---|---|
| Library directories | `assemble_lib_dirs` | `CRANELISP_LIB` entries (colon-separated, empty segments dropped), then `lib-dirs`, then `{project_root}/stdlib` if that directory exists |
| Platform directories | `assemble_platform_dirs` | `CRANELISP_PLATFORM_PATH` entries, then `platform-dirs`. There is no default tier: the project-root and library `platforms/` subdirectories are searched by `src/platform.rs::resolve_platform_path` ahead of this set ([io-integration.md §2.2](io-integration.md#22-search-order)). |

- Duplicates are removed at their first, highest-precedence position. The
  comparison is exact path equality, not canonical-path equality.
- Configured directories that do not exist are kept; only the `stdlib`
  default is existence-filtered.
- `CompilerSession::new` assembles both sets once, when the session is built.

## 3. Failure behaviour

A malformed or unreadable file contributes nothing to either set, and the
session proceeds. The loaders build the diagnostic, but both `assemble_*`
functions discard it, so the user sees none (§5, gap 1).

## 4. Scaffold writer

`scaffold_project_config` writes a default file, rendered by
`render_scaffold_contents`. It is called only by the REPL, and only when the
target was an existing directory (repl-lifecycle.md §6, third case). On
success the REPL prints `[created Cranelisp.toml]`.

- **Content.** Every setting is commented out, so the scaffold changes no
  resolution:
  - a header;
  - a `lib-dirs` example;
  - the current `CRANELISP_LIB` value, when it is set and non-empty;
  - a `platform-dirs` example.
- **Invariants:**
  - **Never overwrite.** The existence check comes first and covers any file,
    directory or link at the path.
  - **Only the project root.** It writes a single file at
    `project_root.join("Cranelisp.toml")`.
  - **Atomic.** The write goes through `save::atomic_write`.
  - **Never fatal.** A write failure returns `Ok(false)`, and the REPL launches
    normally.
  - **No effect on this session.** The scaffold runs after the session is
    built.
  - **REPL-only.** `--run` and `--link` never scaffold.

## 5. Evidence and open gaps

- **Units.** `session_setup.rs` `project_config_tests` cover:
  - the loaders, including the malformed-file diagnostic;
  - union, precedence and deduplication;
  - the scaffold: default content, never overwriting, capturing the
    environment, and a read-only directory.
- **End to end.** Library and platform precedence, and a malformed file not
  crashing, are covered in `tests/spec_platforms.rs`. The scaffold trigger,
  the scaffold not overwriting, and union behaviour are covered in
  `tests/project_config.rs`.

Open gaps, read from source on 2026-09-25. None has a failing test, and `qa`
owns attribution.

1. **Malformed-file diagnostic is swallowed.** §8.11.4 and §8.11.5 item 3
   require a diagnostic naming the file and the parse error. Production shows
   none, and `cranelisp_toml_malformed_does_not_crash` checks only survival.
2. **No programmatic additions ahead of the set.** §8.11.4 source 1 requires
   in-code additions searched first. The session setter `set_lib_dirs`
   replaces the whole set instead, and there is no CLI library flag.
3. **No scaffold-failure warning.** §0.5.7 invariant 3 says a failed scaffold
   SHOULD print one warning naming the directory. None is printed.
