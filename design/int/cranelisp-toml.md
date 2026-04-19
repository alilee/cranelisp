# Cranelisp.toml Project Configuration (Step 5d (iii))

Implementation design for the project-configuration-file lookup that closes `spec/08-modules.md §8.11.4 item 2`.

Spec anchor: `spec/08-modules.md §8.11.4 item 2` ("Project configuration file (e.g., `Cranelisp.toml`) MAY specify a lib directory list. When present, this takes precedence over environment and defaults."). Closes inline `FIXME(/int)` at `spec/08-modules.md:639,648`.

## 1. Problem Statement

The spec describes a four-tier precedence order for lib directory configuration:

1. **Explicit programmatic additions** — highest precedence, prepended to list.
2. **Project configuration file** (`Cranelisp.toml`) — second-highest, fully controls if present.
3. **`CRANELISP_LIB` environment variable** — third, fully controls if set.
4. **Default fallback** — `{project_root}/stdlib/` if it exists.

Today `src/session.rs::assemble_lib_dirs` implements only tiers 3 and 4 (env var + default fallback). Tier 1 (explicit programmatic) is supported via the `SharedState.lib_dirs: Mutex<Vec<PathBuf>>` push API; tier 2 (Cranelisp.toml) is silently ignored.

A `Cranelisp.toml` placed in the project root by a user will not change behaviour — the bug surface is "user puts the config file in place, expects it to work, lib resolution still falls through to env or default." This violates the spec's stated MAY-takes-precedence-when-present semantics.

## 2. Key Design Decisions

### 2.1 File location

**Choice**: `{project_root}/Cranelisp.toml`. The project root is the directory containing the entry `.cl` file (per spec §8.11.1). Lookup is non-recursive — only the project root is consulted; parent directories are NOT searched.

Rationale: keeps lookup deterministic and cheap (one stat). The "project root" is already the anchor for module + platform resolution; Cranelisp.toml inherits that anchor naturally. A future-recursive search (Cargo-style "walk up to find Cargo.toml") is out of scope; if useful it can be added later without breaking the §8.11.4 contract.

### 2.2 File format

**Choice**: TOML. The filename suffix already implies it; the spec example names the file `Cranelisp.toml`.

Initial schema (Sprint 58 minimum):

```toml
# Cranelisp.toml — project configuration

# Lib directory list. Paths are relative to the project root, or absolute.
# Replaces the environment variable and default fallback when present.
lib-dirs = ["stdlib", "../shared-libs"]

# (Future) Platform DLL search directories — §8.11.5 tier 2. Same semantics.
# platform-dirs = ["target/debug"]
```

Two top-level keys planned; only `lib-dirs` is required for Sprint 58 (the spec FIXME is specifically about §8.11.4 item 2). `platform-dirs` follows the same shape if/when `/int` extends to §8.11.5 item 2 (out of scope this sprint).

### 2.3 Crate dependency

**Choice**: add `toml = "0.8"` as a `cranelisp` (binary crate) dependency. The TOML parser lives behind a thin `parse_project_config` helper; `serde::Deserialize` derives the schema struct.

```rust
#[derive(Debug, Deserialize, Default)]
struct ProjectConfig {
    #[serde(default, rename = "lib-dirs")]
    lib_dirs: Vec<PathBuf>,
    // Future:
    // #[serde(default, rename = "platform-dirs")]
    // platform_dirs: Vec<PathBuf>,
}
```

`toml` is mature, widely used (Cargo's own format), and small (no transitive bloat). Considered alternatives: hand-roll a tiny parser (rejected — TOML's escape rules are fiddly), use JSON (rejected — file extension would be wrong, less ergonomic for hand-edit), use a Cranelisp.cl config (rejected — bootstrapping concerns: the config file would have to load before the prelude exists).

### 2.4 Path resolution within the file

**Choice**: paths in `lib-dirs` are relative to the project root, or absolute. Tilde expansion (`~/foo`) is NOT supported (avoid the home-dir-detection complexity for a v1 feature).

Resolution:

```rust
let resolved: Vec<PathBuf> = config.lib_dirs.iter()
    .map(|p| if p.is_absolute() { p.clone() } else { project_root.join(p) })
    .collect();
```

### 2.5 Precedence implementation

`assemble_lib_dirs` becomes:

```rust
pub fn assemble_lib_dirs(project_root: &Path) -> Vec<PathBuf> {
    // Tier 2: Project config file. Highest non-programmatic precedence.
    if let Some(config_dirs) = load_project_config_lib_dirs(project_root) {
        return config_dirs;  // Fully controls — env and default skipped.
    }
    // Tier 3: CRANELISP_LIB env var.
    if let Ok(env_val) = std::env::var("CRANELISP_LIB") {
        return env_val.split(':').filter(|s| !s.is_empty()).map(PathBuf::from).collect();
    }
    // Tier 4: Default fallback.
    let candidate = project_root.join("stdlib");
    if candidate.is_dir() { vec![candidate] } else { Vec::new() }
}
```

Tier 1 (explicit programmatic) is handled by the existing `SharedState.lib_dirs` Mutex API — explicit additions are appended/prepended to whatever `assemble_lib_dirs` returns.

### 2.6 Failure modes

| Condition | Behaviour |
|---|---|
| `Cranelisp.toml` absent | Skip silently; fall through to tier 3. |
| `Cranelisp.toml` present, parse error | Emit a `CranelispError::ConfigError` with the file path, line/column from the TOML parse error, and the spec citation. The compiler exits non-zero. (Do NOT silently fall through — a malformed config file is a user-visible bug.) |
| `Cranelisp.toml` present, valid, `lib-dirs` absent or empty | Treat as "config file says no lib dirs". Skip tiers 3 and 4 — empty list is a valid config-driven choice. (This matches `CRANELISP_LIB=""` which the spec already specifies as "fully controls, no fallback".) |
| `Cranelisp.toml` present, valid, `lib-dirs` paths resolve to non-existent directories | Resolve path is best-effort; non-existent dirs stay in the list. Module resolution will surface "module not found" errors at the import site, which is the spec-defined error path for missing modules. (Don't filter out non-existent dirs at config load — that masks user typos.) |

### 2.7 Loader function placement

**Choice**: `pub fn load_project_config_lib_dirs(project_root: &Path) -> Option<Vec<PathBuf>>` lives in `src/session.rs` adjacent to `assemble_lib_dirs`. The TOML parsing helper `parse_project_config` is a private function nearby.

This keeps the configuration concerns in one file; `assemble_lib_dirs` reads `load_project_config_lib_dirs` first.

## 3. Data Flow

```
binary startup (CLI parses args, identifies entry .cl file)
   │
   ▼
project_root = entry_file.parent() (per §8.11.1)
   │
   ▼
src/session.rs assemble_lib_dirs(project_root)
   │
   ├─ load_project_config_lib_dirs(project_root)
   │     │
   │     ├─ candidate = project_root / "Cranelisp.toml"
   │     ├─ if !candidate.is_file(): return None
   │     ├─ contents = read_to_string(candidate)? (parse error → CranelispError::ConfigError)
   │     ├─ config = toml::from_str::<ProjectConfig>(contents)? (same)
   │     ├─ resolved = config.lib_dirs.iter().map(resolve_relative_to_root).collect()
   │     └─ return Some(resolved)
   │
   ├─ if Some(dirs): return dirs  (tier 2 wins; tier 3+4 skipped)
   ├─ if CRANELISP_LIB set: return env-derived list  (tier 3)
   └─ return [project_root/stdlib] if exists else []  (tier 4)
```

## 4. Affected Files

| File | Change |
|---|---|
| `src/session.rs` | Add `load_project_config_lib_dirs` + `parse_project_config` private helpers. Update `assemble_lib_dirs` to consult tier 2 first. |
| `src/CLAUDE.md` (already in scope) | No change — error handling already prescribes `CranelispError` for user-input failures. |
| `Cargo.toml` (root binary's `[dependencies]`) | Add `toml = "0.8"`. |
| `crates/cranelisp-types/src/error.rs` (or wherever `CranelispError` variants live) | Add `ConfigError { file: PathBuf, message: String, span: Option<Span> }` variant if not already present. (Use existing `ModuleError` if it fits — config-load errors are arguably module-resolution errors.) |
| `tests/e2e.rs` | Add a new test demonstrating Cranelisp.toml lookup — see §6 below. |
| `spec/08-modules.md` | Owner is `/spec`; `/int` files no edit. After landing, `/spec` removes the FIXME at lines 639,648. |

## 5. Edge Cases & Invariants

- **Multiple entry files in different roots**. Each invocation has one project root (per spec §8.11.1); each loads its own config independently. No cross-invocation caching.
- **REPL invocation with no entry file**. The REPL's working directory is the project root (per spec §8.11.1). Cranelisp.toml lookup uses CWD. This is consistent with `--run` behaviour.
- **Symlinked Cranelisp.toml**. Follow symlinks (default `read_to_string` behaviour). No special-casing.
- **UTF-8-only**. TOML 1.0 mandates UTF-8; the `toml` crate enforces this. Non-UTF-8 file → parse error → user-visible diagnostic.
- **Permissions**. If `Cranelisp.toml` exists but is unreadable (perms), surface as parse error with the OS error message. Don't silently fall through.
- **Atomic update during compilation**. Reading the config is a single `read_to_string` call; concurrent writes are at the OS level. No need for file locking — worst case we read a partially-updated file and surface a parse error, which is the same UX as a malformed file. (User edits config in place; restart to see effect.)
- **Empty `lib-dirs` list vs no `lib-dirs` key**. `lib-dirs = []` returns `Some(vec![])` from the loader → fully overrides → empty lib list (matches `CRANELISP_LIB=""` semantics). `lib-dirs` absent (key not in file) → also `Some(vec![])` due to `serde(default)` → same behaviour. Both forms mean "config-driven empty list."

  If a use case emerges where "config file present but no opinion on lib-dirs" should fall through to env/default, we can distinguish via `Option<Vec<PathBuf>>` in the schema. Out of scope; the spec wording ("MAY specify a lib directory list") doesn't require the distinction.

## 6. Test Contract

New `tests/e2e.rs` test:

```rust
// spec: 08-modules §8.11.4 item 2 — project config file precedence
#[test]
fn e2e_cranelisp_toml_lib_dirs_overrides_default() {
    let tmpdir = tempfile::tempdir().unwrap();
    let proj = tmpdir.path();

    // Set up an alt-stdlib outside the default {project_root}/stdlib path,
    // with a uniquely-named module.
    let alt_stdlib = proj.join("vendor-libs");
    std::fs::create_dir_all(&alt_stdlib).unwrap();
    std::fs::write(alt_stdlib.join("custom-helper.cl"),
        "(defn answer [] 42)").unwrap();

    // Cranelisp.toml points lib-dirs at the alt location.
    std::fs::write(proj.join("Cranelisp.toml"),
        r#"lib-dirs = ["vendor-libs"]"#).unwrap();

    // Entry file imports the alt-stdlib module by bare name (lib lookup).
    std::fs::write(proj.join("main.cl"),
        "(import [custom-helper [answer]])\n(defn main [] (answer))").unwrap();

    // CRANELISP_LIB explicitly set to a wrong directory to prove tier 2 wins.
    let result = helpers::batch_run_file_with_env(
        &proj.join("main.cl"),
        &[("CRANELISP_LIB", "/nonexistent/path")],
    );
    assert!(result.is_ok(), "Cranelisp.toml lib-dirs MUST take precedence over CRANELISP_LIB");
    assert_eq!(result.unwrap(), 42);
}
```

A second test verifies absent-config-file behaviour preserves the existing env/default tiers (sanity check that tier 2 is genuinely additive, not displacing).

## 7. Cross-Skill Coordination

| Skill | Coordination |
|---|---|
| `/spec` | Removes the FIXME at `spec/08-modules.md:639,648` after the test passes and the implementation lands. The annotation at §8.11.4 updates from `[Tested ... env var; project-config file NOT YET IMPLEMENTED]` to `[Tested ... env var; project config file]`. |
| `/qa` | Reviews the test in `tests/e2e.rs`; possibly extends with negative-path tests (malformed Cranelisp.toml emits diagnostic; absent file falls through correctly). |
| `/docs` | If `user/` documentation references project config, refresh to mention `Cranelisp.toml`. The Sprint 58 SPRINT.md `/docs` task already flags this. |

## 8. Sketch Comparison

The sketch did NOT have a project configuration file. It implemented only `CRANELISP_LIB` and the `{project_root}/stdlib/` default. There is no sketch precedent for `Cranelisp.toml`; this is a spec-defined feature added during the Phase A spec review (sketch was a pre-spec prototype).

This is a "sketch did not have this; this is new" case per `/arch`'s Sketch Consultation rules. The design above derives entirely from the spec wording and the existing `assemble_lib_dirs` shape; no sketch consultation was required because the sketch's `assemble_lib_dirs` equivalent (a env-and-default-only function) is already what the reimplementation has.

## 9. Open Questions

- **Multi-key file format vs single-purpose file**. Should `Cranelisp.toml` accommodate non-lib-dirs config in v1 (e.g., `[build]` or `[repl]` sections)? The spec mentions `lib-dirs` and `platform-dirs` (§8.11.5 item 2); other keys are speculative. The schema struct above accommodates `lib_dirs` as the only required key; new keys can be added without breaking older configs (TOML is forgiving, `serde(default)` handles missing fields). No need to over-design for v1.
- **Where to surface the config-file path on error**. The error message includes the file path; whether to include the full TOML parse-error span (line:col) depends on the `toml` crate's error message shape. The crate's `Error::span()` API returns this — include it.
- **Validation beyond parse**. Should `lib-dirs` paths be validated to exist at config-load time? Per §5 above: no — let module resolution surface the missing-module error at use time, which is the spec-defined error path. Filtering at load would mask typos.

## 10. Next Skills

- `/qa` — confirm new e2e test passes; consider negative-path tests.
- `/spec` — remove the FIXME(/int) at §8.11.4; update annotation to drop "NOT YET IMPLEMENTED".
- `/docs` — refresh `user/` if any user-facing documentation mentions project config.
