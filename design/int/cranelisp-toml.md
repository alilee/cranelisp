# Cranelisp.toml Project Configuration (Step 5d (iii))

Implementation design for the project-configuration-file lookup that closes `spec/08-modules.md §8.11.4 item 2`.

Spec anchor: `spec/08-modules.md §8.11.4 item 2` ("Project configuration file (e.g., `Cranelisp.toml`) MAY specify a lib directory list."). Closes inline `FIXME(/int)` at `spec/08-modules.md:639,648`.

> **S91 model correction (FIXME 0410).** `/spec` re-ruled §8.11.4/§8.11.5 (settled S91): the resolved lib-dir set is the **additive UNION** of all sources — `Cranelisp.toml` `lib-dirs` only ever **ADDS** paths; it never *replaces* or *suppresses* `CRANELISP_LIB`, the programmatic additions, or the `{project_root}/stdlib/` default. The original "fully-replaces / first-tier-wins" precedence text below (§§2.5–2.6, §3 data-flow, §5 edge-cases, §6 test contract) is **superseded** by §11 (additive resolution) and §12 (the `Cranelisp.toml` scaffold writer). The stale paragraphs are retained for narrative continuity but are NOT the live contract — read §§11–12 first.

## 1. Problem Statement

> **S91 rewrite (FIXME 0435).** This section originally described a four-tier
> *replacing-precedence* model ("config file fully controls if present"). That
> model was **retired** by `/spec`'s settled additive-UNION ruling
> (`spec/08-modules.md §8.11.4`, S91, FIXME 0410). The text below is the
> rewritten additive statement; §11 is the normative resolution design.

The spec defines lib directory resolution as the **additive UNION of four
sources** — no source ever replaces or suppresses another; each only ever
*contributes*:

1. **Explicit programmatic / CLI additions** — highest *search-order* precedence.
2. **`CRANELISP_LIB` environment variable** — colon-separated list, contributes its entries.
3. **Project configuration file** (`Cranelisp.toml`) `lib-dirs` — only ADDS paths.
4. **Default** — `{project_root}/stdlib/` if it exists; contributes like any other source.

The resolved set is the order-preserving, deduplicated union of all four; on a
module name present in more than one directory, **first-match wins** in that
order (so `CRANELISP_LIB` precedes the toml file — env over config, Cargo
convention).

Today `src/session_setup.rs::assemble_lib_dirs` implements the env var + default
sources but folds the project-config tier with an **early return** (the retired
"replaces" behaviour). The bug surface is twofold: (a) `Cranelisp.toml` placed in
the project root does not *add* its dirs to the env/default set (it replaces
them); (b) a present-but-empty config silently *suppressed* the `{root}/stdlib/`
default — the footgun the additive ruling dissolves. The implementation fold must
become an order-preserving union with dedup (§11.2).

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
# Entries here are ADDED to the resolved set (union with CRANELISP_LIB and
# {project-root}/stdlib/); they never replace or suppress those sources
# (additive model — spec §8.11.4, settled S91 / FIXME 0410).
lib-dirs = ["stdlib", "../shared-libs"]

# Platform DLL search directories — §8.11.5. Same additive semantics
# (union with CRANELISP_PLATFORM_PATH; only adds).
# platform-dirs = ["target/debug"]
```

Two top-level keys: `lib-dirs` and `platform-dirs`. Both are optional and both
are *additive* sources under the §8.11.4/§8.11.5 union — an absent key, an absent
file, and `key = []` are all equivalent (each contributes nothing, removes
nothing). The `platform-dirs` key was dormant in the original Sprint-58 design and
is **activated** by the same FIXME 0410 ruling (see §11.2 note).

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

### 2.5 Resolution implementation (additive union)

> **S91 rewrite (FIXME 0435).** The original code below returned early on the
> config tier (`return config_dirs; // Fully controls`) — the retired replacing
> model. The corrected fold UNIONs all sources with order-preserving dedup. The
> normative version is §11.2; this is the in-line sketch.

`assemble_lib_dirs` becomes an order-preserving union, NOT a first-non-empty
early-return:

```rust
pub fn assemble_lib_dirs(project_root: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    let mut seen: std::collections::HashSet<PathBuf> = std::collections::HashSet::new();
    let mut add = |p: PathBuf| {
        let key = p.canonicalize().unwrap_or_else(|_| p.clone());
        if seen.insert(key) { out.push(p); }
    };

    // Source 2: CRANELISP_LIB env var (searched BEFORE the toml file — env over config).
    if let Ok(env_val) = std::env::var("CRANELISP_LIB") {
        for s in env_val.split(':').filter(|s| !s.is_empty()) { add(PathBuf::from(s)); }
    }
    // Source 3: Cranelisp.toml lib-dirs (only ADDS; Ok(None)/empty contributes nothing).
    if let Ok(Some(config_dirs)) = load_project_config_lib_dirs(project_root) {
        for d in config_dirs { add(d); }
    }
    // Source 4: {project_root}/stdlib/ default (contributes if it exists; not a fallback).
    let candidate = project_root.join("stdlib");
    if candidate.is_dir() { add(candidate); }

    out
}
```

Source 1 (explicit programmatic / CLI) is layered *ahead* of this set by callers
via the `SharedState.lib_dirs` API — those additions take the highest search-order
position. (See §11.2 for the normative statement and the dedup contract.)

### 2.6 Failure modes

| Condition | Behaviour |
|---|---|
| `Cranelisp.toml` absent | `load_project_config_lib_dirs` returns `Ok(None)`; the config source contributes nothing to the union (env + default still contribute). |
| `Cranelisp.toml` present, parse error | Emit a `CranelispError::ModuleError` with the file path, the TOML parse error, and the spec citation (current impl, §2.x). A malformed config file is a user-visible bug. |
| `Cranelisp.toml` present, valid, `lib-dirs` absent or empty | Contributes nothing and **removes nothing** — the env source and the `{root}/stdlib/` default still contribute (additive model, FIXME 0435). Equivalent to an absent file. (NOT the retired "config says no lib dirs, skip env/default" behaviour.) |
| `Cranelisp.toml` present, valid, `lib-dirs` paths resolve to non-existent directories | Resolve path is best-effort; non-existent dirs stay in the list. Module resolution will surface "module not found" errors at the import site, which is the spec-defined error path for missing modules. (Don't filter out non-existent dirs at config load — that masks user typos.) |

### 2.7 Loader function placement

**Choice**: `pub fn load_project_config_lib_dirs(project_root: &Path) -> Option<Vec<PathBuf>>` lives in `src/session.rs` adjacent to `assemble_lib_dirs`. The TOML parsing helper `parse_project_config` is a private function nearby.

This keeps the configuration concerns in one file; `assemble_lib_dirs` reads `load_project_config_lib_dirs` first.

## 3. Data Flow

> **S91 rewrite (FIXME 0435).** The terminal "tier 2 wins; tier 3+4 skipped"
> branch below was the retired replacing model. Under the additive union every
> source is folded into one set (env → toml → default), order-preserving + dedup.

```
binary startup (CLI parses args, identifies entry .cl file)
   │
   ▼
project_root = entry_file.parent() (per §8.11.1)
   │
   ▼
src/session_setup.rs assemble_lib_dirs(project_root)  →  ORDER-PRESERVING UNION
   │
   ├─ source 2: CRANELISP_LIB entries  ──┐
   ├─ source 3: load_project_config_lib_dirs(project_root)
   │     ├─ candidate = project_root / "Cranelisp.toml"
   │     ├─ if !candidate.is_file(): Ok(None)            (contributes nothing)
   │     ├─ contents = read_to_string(candidate)?        (read err → ModuleError)
   │     ├─ config = toml::from_str::<ProjectConfig>(..)? (parse err → ModuleError)
   │     ├─ resolved = config.lib_dirs.map(resolve_relative_to_root)
   │     └─ Ok(Some(resolved))   (may be empty — contributes nothing, removes nothing)
   │                                       │
   ├─ source 4: [project_root/stdlib] if it exists  ─────┤
   │                                       ▼
   └─ UNION(source2, source3, source4) with first-occurrence dedup
        (source 1 = CLI/programmatic is layered ahead by callers)
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
- **Empty `lib-dirs` list ≡ absent key ≡ absent file** (additive model, FIXME 0435). `lib-dirs = []` returns `Some(vec![])` from the loader; an absent key also returns `Some(vec![])` via `serde(default)`; an absent file returns `Ok(None)`. Under the union fold (§11.2) **all three contribute nothing and remove nothing** — they leave the `CRANELISP_LIB` and `{root}/stdlib/` sources fully intact. (This is the inverse of the retired "empty-replaces / config-driven empty list" behaviour: there is no replacing tier, so the `Option<Vec<PathBuf>>` "present-but-no-opinion" distinction the original design pondered is **moot** — see §9.)

## 6. Test Contract

> **S91 rewrite (FIXME 0435).** The original contract asserted "Cranelisp.toml
> `lib-dirs` MUST take **precedence over** `CRANELISP_LIB`" — a *replacing*
> assertion that is **wrong** under the additive union. Two corrections: (a) a
> toml dir is *added* to (not substituted for) the env/default set; (b) on a
> module-name collision across dirs, the **search-order winner is the env entry**
> (`CRANELISP_LIB` is searched *before* the toml file), not the toml dir. The
> `/qa` e2e was re-aligned this wave to the additive shape
> (`lib_dir_resolution_is_additive_env_before_toml`).

New `tests/e2e.rs` test — proves a toml dir is *added* (a module reachable only
via the toml dir resolves even when `CRANELISP_LIB` is also set to a real,
different dir):

```rust
// spec: 08-modules §8.11.4 — Cranelisp.toml lib-dirs is ADDITIVE (union), not replacing
#[test]
fn lib_dir_resolution_is_additive_env_before_toml() {
    let tmpdir = tempfile::tempdir().unwrap();
    let proj = tmpdir.path();

    // A module reachable ONLY via the toml-named dir.
    let toml_dir = proj.join("vendor-libs");
    std::fs::create_dir_all(&toml_dir).unwrap();
    std::fs::write(toml_dir.join("toml-only.cl"),
        "(defn answer [] 42)").unwrap();

    // A REAL, different env dir (proves it is NOT suppressed by the toml file).
    let env_dir = proj.join("env-libs");
    std::fs::create_dir_all(&env_dir).unwrap();

    std::fs::write(proj.join("Cranelisp.toml"),
        r#"lib-dirs = ["vendor-libs"]"#).unwrap();

    // toml-only module resolves BECAUSE the toml dir is ADDED to the set,
    // even with a real (non-empty) CRANELISP_LIB in play.
    std::fs::write(proj.join("main.cl"),
        "(import [toml-only [answer]])\n(defn main [] (answer))").unwrap();

    let result = helpers::batch_run_file_with_env(
        &proj.join("main.cl"),
        &[("CRANELISP_LIB", env_dir.to_str().unwrap())],
    );
    assert!(result.is_ok(), "toml lib-dir is ADDED to the union, not replaced by CRANELISP_LIB");
    assert_eq!(result.unwrap(), 42);
}
```

Companion assertions the union contract requires (see also §11.3 unit tests):
- **Env-before-toml on collision.** A module name present in *both* the env dir
  and the toml dir resolves to the **env** copy (first-match search order), not
  the toml copy — the corrected precedence direction.
- **Empty/absent config removes nothing.** `lib-dirs = []` (or absent key, or
  absent file) with `CRANELISP_LIB` + `{root}/stdlib/` present ⇒ both still
  resolve (the additive-not-suppressing guard).
- **Dedup.** A dir named in both `CRANELISP_LIB` and the toml file appears once,
  at the earlier (env) position.

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

- **~~Distinguishing "present but no opinion" via `Option<Vec<PathBuf>>`~~ — RESOLVED (moot under the union, FIXME 0435).** The original design left open whether a present file with no `lib-dirs` opinion should fall through to env/default via an `Option` schema. Under the additive model there is **no replacing tier to fall through from**: an absent key, an absent file, and `lib-dirs = []` are all already equivalent (each contributes nothing, removes nothing — §5, §11.2). The `Vec` + `serde(default)` schema is correct as-is; no `Option` distinction is needed.
- **Multi-key file format vs single-purpose file**. Should `Cranelisp.toml` accommodate non-lib-dirs config in v1 (e.g., `[build]` or `[repl]` sections)? The spec defines `lib-dirs` (§8.11.4) and `platform-dirs` (§8.11.5); other keys are speculative. The schema struct accommodates `lib_dirs` + `platform_dirs`; new keys can be added without breaking older configs (TOML is forgiving, `serde(default)` handles missing fields). No need to over-design for v1.
- **Where to surface the config-file path on error**. The error message includes the file path; whether to include the full TOML parse-error span (line:col) depends on the `toml` crate's error message shape. The crate's `Error::span()` API returns this — include it.
- **Validation beyond parse**. Should `lib-dirs` paths be validated to exist at config-load time? Per §5 above: no — let module resolution surface the missing-module error at use time, which is the spec-defined error path. Filtering at load would mask typos.

## 10. Next Skills

- `/qa` — confirm new e2e test passes; consider negative-path tests.
- `/spec` — remove the FIXME(/int) at §8.11.4; update annotation to drop "NOT YET IMPLEMENTED".
- `/docs` — refresh `user/` if any user-facing documentation mentions project config.

---

## 11. Additive resolution model (FIXME 0410, settled S91) — supersedes §§2.5–2.6

`/spec` re-ruled §8.11.4/§8.11.5: **the resolved lib-directory set is the additive UNION of all four sources.** No source ever replaces or suppresses another; each only ever *contributes*. This dissolves the §2.5 "first non-empty tier fully controls" model and the §2.6 "config present ⇒ skip env/default" footgun entirely.

### 11.1 The union (what `assemble_lib_dirs` must produce)

The set is the union of, in **search order** (first-match precedence on a name present in more than one dir):

1. **Programmatic / CLI additions** — `SharedState.lib_dirs` push API + any CLI lib-dir flag.
2. **`CRANELISP_LIB`** entries (colon-separated), in their listed order.
3. **`Cranelisp.toml` `lib-dirs`** entries (resolved relative to the project root), in their listed order. **Only adds.**
4. **`{project_root}/stdlib/`** default, *if it exists* — searched **last**, contributes like any other source (it is no longer a fallback that an earlier source turns off).

Spec note: env (`CRANELISP_LIB`) precedes the config file in *search order* (Cargo convention — env over config) but **neither suppresses the other**; both contribute, and the default `{root}/stdlib/` always contributes when present.

### 11.2 Design implication for `load_project_config_lib_dirs` + `assemble_lib_dirs`

`load_project_config_lib_dirs` is unchanged in shape — it still returns `Ok(None)` for an absent file, `Ok(Some(resolved))` for a present (possibly empty) file, `Err` for malformed. **What changes is how the caller folds the result:** instead of the early-return `if let Ok(Some(dirs)) = … { return dirs; }` (which made the config file *replace* the env/default tiers), `assemble_lib_dirs` must **concatenate-with-dedup** all four sources in the §11.1 order. An absent `lib-dirs` key, an absent `Cranelisp.toml`, and `lib-dirs = []` are now all equivalent: each contributes nothing and removes nothing (the spec's §8.11.4-item-3 equivalence). The `ProjectConfig` doc-comment claiming "fully replaces the env/default tiers" is stale and must be corrected when the union fold lands.

Dedup: a directory contributed by more than one source appears once, at its **earliest** (highest-precedence) position, so first-match search order is preserved. (`/dev` choice: an order-preserving `Vec` + `HashSet<PathBuf>` seen-set over canonicalized paths, or simple `dedup` after sort-by-first-occurrence.)

> **Note** — the same additive union now governs **platform** dirs (§8.11.5): `assemble_platform_dirs` gains the `Cranelisp.toml` `platform-dirs` tier as an *additive* source, mirroring §11.1 (CLI/programmatic → `CRANELISP_PLATFORM_PATH` → toml `platform-dirs`, no default tier). The `ProjectConfig` schema struct grows a `#[serde(default, rename = "platform-dirs")] platform_dirs: Vec<PathBuf>` field. This is the dormant `platform-dirs` key promised in §2.2, now activated by the same FIXME 0410 ruling.

### 11.3 `/dev` acceptance (additive resolution)

- **Unit (`session_setup.rs` `#[cfg(test)]`):** a `Cranelisp.toml` with `lib-dirs = ["vendor"]` + `CRANELISP_LIB=/env/dir` + an existing `{root}/stdlib/` ⇒ `assemble_lib_dirs` returns **all three** (`/env/dir`, `{root}/vendor`, `{root}/stdlib`) in §11.1 order — NOT just the config dir. The existing `assemble_lib_dirs_project_config_overrides_env_var` test (which asserts the config dir *replaces* env) is **retired/re-written** to assert union membership + ordering.
- **Unit (negative):** `lib-dirs = []` (or absent key) with `CRANELISP_LIB` set ⇒ the env dir is still present (empty config removes nothing).
- **Unit (dedup):** the same dir named in both `CRANELISP_LIB` and `lib-dirs` appears once, at the env (earlier) position.

---

## 12. `Cranelisp.toml` scaffold writer (FIXME 0410 — the int writer half)

When the REPL is pointed at a **project-root directory** (spec §0.5 rule 3 — `cranelisp myproject` where `myproject/` exists and `myproject.cl` does not) that lacks a `Cranelisp.toml`, the binary scaffolds a default one: a discoverable, editable config (the `cargo`/`git init` ergonomic). This is the int *writer* half. The **UX/trigger half** (the `[created Cranelisp.toml]` REPL notice + the §0.5 trigger wiring) is `/repl`'s — this section designs the file-writing mechanism only and stays consistent with it.

### 12.1 Function placement

A new free function beside `load_project_config_lib_dirs` in `src/session_setup.rs`:

```rust
/// Scaffold a default `{project_root}/Cranelisp.toml` if (and only if) one
/// does not already exist. Returns Ok(true) if a file was newly created,
/// Ok(false) if one already existed (no-op), Err only on a write failure the
/// caller chooses to surface (it does NOT — see §12.4).
///
/// Spec: 08-modules.md §8.11.4 (additive model) + repl/spec.md §0.5 rule 3.
pub fn scaffold_project_config(project_root: &Path) -> std::io::Result<bool>
```

The REPL trigger (`/repl`'s half) calls this once, only on the §0.5-rule-3 directory-target path, and renders its own notice from the `Ok(true)` return. `scaffold_project_config` itself emits **no** output (warnings are data, not side effects — `src/CLAUDE.md`).

### 12.2 Scaffold content (per the user decision)

The generated file carries the **current `CRANELISP_LIB` paths COMMENTED OUT** (visible so the user knows what was in effect at scaffold time, uncommentable to make permanent) plus a commented schema template. **No machine-specific path is ever written as live config** — the active key set is empty, so the scaffold is resolution-neutral by construction (and trivially safe under the §11 additive model — an empty/absent `lib-dirs` removes nothing).

Template (illustrative — exact prose is `/dev`'s, this pins the shape):

```toml
# Cranelisp.toml — project configuration (auto-created)
#
# Lib directories. Paths are relative to this file's directory, or absolute.
# Under the additive model (spec §8.11.4), entries here are ADDED to the set
# already resolved from CRANELISP_LIB and {project-root}/stdlib/ — they never
# replace or suppress those sources. Uncomment to make a path permanent.
#
# lib-dirs = [
#   "stdlib",          # example: a vendored stdlib beside this file
# ]

# Captured from CRANELISP_LIB at scaffold time (commented — uncomment to pin):
# lib-dirs = ["/abs/from/env/a", "/abs/from/env/b"]

# Platform DLL search dirs (§8.11.5). Same additive semantics.
# platform-dirs = ["target/debug"]
```

The `CRANELISP_LIB`-capture line is emitted **only when `CRANELISP_LIB` is set and non-empty**; when unset, that block is omitted (or rendered as a generic commented example). Because every key is commented, `toml::from_str` of the scaffold yields the `ProjectConfig::default()` (all-empty) — i.e. **the scaffold is a no-op for resolution**: prelude/stdlib resolve exactly as they did with no file at all (this is the additive model's guarantee, and is the acceptance below).

### 12.3 Invariants (the pins)

| Invariant | Mechanism |
|---|---|
| **Never overwrite** | `if project_root.join("Cranelisp.toml").exists() { return Ok(false); }` is the first statement. An existing file (any content) is left verbatim. Idempotent: a second launch is a no-op. |
| **Never write outside the resolved project root** | The path is `project_root.join("Cranelisp.toml")` — a single non-recursive join, no `..`, no symlink-following beyond the OS default. `project_root` is the §0.5-rule-3-resolved root, already validated by the caller. |
| **Graceful on read-only dir** | A write failure (`EACCES`, read-only FS) is caught; the function returns `Err` (or `Ok(false)` — `/dev` choice), and the **caller must NOT fail the REPL launch** — it logs a one-line warning (`/repl`'s notice text) and proceeds with the absent-file resolution path (which is well-defined and unchanged). The scaffold is a convenience, never a launch gate. |
| **Atomicity** | Reuse `save::atomic_write` (temp-then-rename) so a crash mid-write cannot leave a truncated `Cranelisp.toml`. The never-overwrite check makes the temp-file race benign (we only ever create, never replace). |
| **REPL-only** | Only the REPL §0.5-rule-3 path calls this. `--run`/`--link` never mutate the project tree as a compile side effect (`/repl`'s scope decision; the writer simply is not called from batch paths). |

### 12.4 `/dev` acceptance (scaffold writer)

- **Unit (creates):** `scaffold_project_config(tmp)` on a dir with no `Cranelisp.toml` ⇒ `Ok(true)`, the file now exists, and `toml::from_str::<ProjectConfig>` of its contents parses to `ProjectConfig::default()` (every key commented ⇒ all-empty).
- **Unit (no-overwrite / idempotent):** with a pre-existing `Cranelisp.toml` of arbitrary content, `scaffold_project_config` ⇒ `Ok(false)` and the file is **byte-identical** to before (verbatim). A second call after a successful create ⇒ `Ok(false)`.
- **Unit (CRANELISP_LIB capture, `#[serial]`):** with `CRANELISP_LIB=/x:/y` set, the scaffold contains a **commented** line carrying `/x` and `/y`; with `CRANELISP_LIB` unset, no such live or commented machine-path line is emitted. (Asserts the "visible, commented, uncommentable" decision + the "no machine path as live config" pin.)
- **Unit (read-only dir):** scaffolding into a read-only directory does **not** panic and does **not** return a launch-fatal error — it returns the graceful variant; a follow-up `assemble_lib_dirs` on that dir still resolves the env/default tiers.
- **e2e (resolution UNCHANGED by the scaffold):** launch the REPL on a bare project dir (§0.5 rule 3) with `{root}/stdlib/prelude.cl` present; assert (a) `Cranelisp.toml` is created, and (b) the prelude/stdlib **still resolve** — i.e. the additive set with the all-commented scaffold == the set with no file at all. This is the keystone: the scaffold must be resolution-neutral.

Principle citations: **Principle 7 (single source of truth)** — `load_project_config_lib_dirs` stays the one config reader; the scaffold writer is a sibling, not a parallel parser. **Principle 6 (complexity has a budget)** — the writer is one never-overwrite-guarded `atomic_write`; no template engine, no merge logic.
