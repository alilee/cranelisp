# Deployment Environment

## 1. Motivation

Cranelisp's current module system resolves all imports relative to the project root — the parent directory of the entry file. The standard library is discovered by heuristic: `$CRANELISP_LIB` → `{project}/lib` → `CARGO_MANIFEST_DIR/lib`. Platform DLLs follow a separate ad-hoc search: `./platforms/` → `target/{debug,release}/` → `~/.cranelisp/platforms/`. There is no configuration file, no inter-project dependency mechanism, and no versioning.

This works for single-developer in-tree development, but breaks down in several ways:

- **Sharing code between projects** — no way to declare that project A depends on a module defined in project B, or on a published package.
- **Reproducible builds** — two machines may resolve different versions of the same module depending on filesystem layout and environment variables.
- **Remote packages** — no mechanism to fetch modules from the network.
- **Platform auditing** — platform DLLs execute native code. The current search order is implicit and non-configurable; a project cannot prioritise trusted local platforms over public ones.
- **Fragmented search** — modules and platforms use entirely separate resolution logic, configured in different ways.

The existing infrastructure provides a solid foundation: the module graph handles dependency ordering and cycle detection, the two-tier cache provides per-module compilation artifacts, and the platform loading system handles DLL discovery and ABI validation. What's missing is a project-level configuration layer that makes resolution explicit, reproducible, and extensible to remote sources.

Reference languages: Cargo/crates.io (Rust), `deps.edn`/Clojars (Clojure), `go.mod`/proxy.golang.org (Go).

## 2. Design Philosophy

**Convention by default, configuration is definitive.** Projects without a `cranelisp.toml` file work exactly as today — the entry file determines the project root, the standard library is discovered by heuristic, platforms are found by ad-hoc search. Adding a `cranelisp.toml` does not extend the existing heuristics; it *replaces* them beyond the project root. The search path declared in the file is the complete, authoritative resolution order. No hidden fallbacks.

**One search path for everything.** Modules (`.cl` source files) and platforms (compiled Rust crate DLLs) share a single ordered search path. Earlier entries shadow later entries. This gives projects and enterprises explicit control over which code — especially native platform code — they trust. A project-local `./vendor/` entry takes priority over a public repository URL.

**Search path resolves, deps constrain.** The search path says *where* to look for packages. The optional `[deps]` section says *which versions* are acceptable. The lockfile records *exactly which* versions were chosen. These are three distinct concerns with clear separation.

**Reproducible builds.** The lockfile pins resolved versions and source hashes. Source caching enables offline builds from remote repositories.

**No central registry required.** Packages are identified by name, discovered on the search path. Any HTTP file server with the right directory layout can host a package repository. A central registry is a convenience, not a requirement.

**Standard library is just a search path entry.** Consistent with the "optional prelude" design principle: the stdlib is not special. If a project's search path omits it, it isn't found. Most projects will include `$CRANELISP_LIB` as the last entry.

## 3. Project Configuration File

### File Format

**`cranelisp.toml`** — TOML format. Human-readable key-value structure, widely supported by editors and tooling, consistent with the Rust ecosystem. S-expression config was considered, but TOML is better suited to flat metadata and avoids overloading `.cl` for non-program files.

The compiler looks for `cranelisp.toml` in the project root (parent directory of the entry file, or CWD for the bare REPL). If absent, all behavior is unchanged from today.

### `[project]` Section

```toml
[project]
name = "my-app"
version = "0.1.0"
description = "A cranelisp application"
entry = "main.cl"
prelude = "prelude.cl"
```

| Field | Default | Description |
|-------|---------|-------------|
| `name` | directory name | Package identity for publishing and lockfile entries |
| `version` | `"0.0.0"` | Semantic version (see Section 6) |
| `description` | none | Human-readable package description |
| `entry` | `"user.cl"` | Entry file for `cranelisp --run` (relative to project root) |
| `prelude` | auto-discover | Explicit prelude path, or `false` to disable |

The `entry` field replaces the current positional CLI argument convention for batch mode. When `cranelisp --run` is invoked in a directory with `cranelisp.toml`, it uses the configured entry point.

The `prelude` field overrides auto-discovery. Setting `prelude = false` suppresses the implicit `(import [prelude [*]])` injection, consistent with the optional prelude principle.

### `search-path` — The Core of the Design

An ordered array of resolution locations. Each entry is one of three kinds:

- **Local path** — a filesystem directory, absolute or relative to project root
- **Environment variable** — `$NAME` syntax, expanded at build time to a filesystem path
- **Web URL** — an HTTP(S) URL pointing to a package repository

```toml
search-path = [
  "./vendor",                              # project-local overrides (highest priority)
  "$COMPANY_CL_LIBS",                      # enterprise packages
  "https://packages.cranelisp.org/",       # public repository
  "$CRANELISP_LIB",                        # standard library (lowest priority)
]
```

When a module or platform name is not found within the project root (steps 1-3 of intra-project resolution), entries are tried in declared order. The first match wins.

This single list replaces both `find_lib_dir()` (for modules) and `resolve_platform_path()` (for platforms). Both module `.cl` files and platform DLLs are discovered on the same path. See Section 4 for the full resolution algorithm.

### `[deps]` Section (Optional)

Version constraints applied to packages found on the search path:

```toml
[deps]
collections-extra = "^0.2"
http-client = "1.3.0"
math-utils = ">=1.0, <3.0"
```

These do **not** add to the search path. They constrain which versions are acceptable when a package with that name is encountered during search path resolution. Without `[deps]`, the latest version found is used and recorded in the lockfile.

The `[deps]` section is optional — a project that uses only local path and environment variable entries on the search path, where packages have no versioning, needs no `[deps]` at all.

### `[features]` Section

Feature flags for conditional compilation:

```toml
[features]
default = ["json"]
json = []
xml = []
full = ["json", "xml"]
```

See Section 8 for feature flag semantics.

### Complete Example

```toml
[project]
name = "web-service"
version = "0.3.1"
description = "A web service built with cranelisp"
entry = "main.cl"

search-path = [
  "./vendor",
  "$COMPANY_CL_LIBS",
  "https://packages.cranelisp.org/",
  "$CRANELISP_LIB",
]

[deps]
http-server = "^2.0"
json-parser = "^1.5"
logging = "^0.3"

[features]
default = ["json"]
json = []
xml = []
```

## 4. Search Path Resolution

### Without `cranelisp.toml` (Unchanged)

The current resolution algorithm from `src/module.rs`:

1. **Child directory** — `parent_dir/stem/name.cl`
2. **Sibling** — `parent_dir/name.cl`
3. **Project root** — `project_root/name.cl`
4. **Library directory** — via `find_lib_dir()` heuristic (`$CRANELISP_LIB` → `{project}/lib` → `CARGO_MANIFEST_DIR/lib`)

Platform DLLs follow a separate path via `resolve_platform_path()`:

1. `./platforms/{name}.{ext}`
2. `target/debug/lib{crate_name}.{ext}`
3. `target/release/lib{crate_name}.{ext}`
4. `~/.cranelisp/platforms/{name}.{ext}`

### With `cranelisp.toml` (Definitive)

Steps 1-3 are unchanged (intra-project resolution):

1. **Child directory** — `parent_dir/stem/name.cl`
2. **Sibling** — `parent_dir/name.cl`
3. **Project root** — `project_root/name.cl`

Step 4 replaces **both** the module `find_lib_dir()` and platform `resolve_platform_path()` heuristics:

4. **Search path entries**, in declared order. For each entry:

   **Local path or expanded environment variable:**
   - Module: check `{path}/{name}.cl`
   - Module with submodules: check `{path}/{name}/` directory
   - Platform: check `{path}/platforms/{triple}/{name}.{ext}`

   **Web URL:**
   - Check `{url}/{name}/versions.json` (see Section 5)
   - If found, apply version constraint from `[deps]` (or use latest)
   - Fetch package source to local source cache
   - Resolve as local path from cache

### No Implicit Fallback

With `cranelisp.toml` present, there is no fallback beyond the declared search path. If the standard library should be available, its location must appear in `search-path`:

```toml
search-path = [
  "$CRANELISP_LIB",     # stdlib — must be explicit
]
```

A minimal `cranelisp.toml` with an empty `search-path` produces a project with no external modules — only the project's own files.

### Shadowing

First match wins. A project can override any module or platform by placing it earlier in the search path:

```toml
search-path = [
  "./patches",                         # local fix for collections-extra
  "https://packages.cranelisp.org/",   # public repo (collections-extra also here)
  "$CRANELISP_LIB",
]
```

If `./patches/collections-extra.cl` exists, it shadows the version on the public repository.

### Security Model

Platforms execute native code — they are the primary attack surface. The search path order is the trust hierarchy:

1. **Project-local** (`./vendor`, `./platforms`) — fully audited, checked into source control
2. **Enterprise** (`$COMPANY_CL_LIBS`) — vetted by the organisation
3. **Public** (`https://packages.cranelisp.org/`) — community-maintained, less trusted

A compromised public platform DLL cannot affect a project that provides its own platform earlier in the search path. This is explicit and auditable — there are no implicit search locations that could be exploited.

### Source Caching for Remote Entries

Remote sources are fetched to a local cache for reliability and offline use:

```
~/.cranelisp/source-cache/
  {url-hash}/
    {package-name}/
      {version}/
        cranelisp.toml
        module.cl
        ...
```

- `cranelisp fetch` — download all remote dependencies to local source cache
- `cache-sources = true` in `[project]` — eagerly cache all remote sources on every build
- Compilation always produces artifacts in the project's `.cranelisp-cache/` — compute is cheap, and this avoids cross-project cache coherence issues

## 5. Package Repository (HTTP)

A package repository is any HTTP server with the following directory layout. No special server software is needed — a static file server (nginx, S3, GitHub Pages) is sufficient.

### URL Structure

```
https://repo.example.com/
  {package-name}/
    versions.json
    {version}/
      cranelisp.toml
      {module}.cl
      {subdir}/{module}.cl
      platforms/
        aarch64-apple-darwin/
          {name}.dylib
        x86_64-unknown-linux-gnu/
          lib{name}.so
        x86_64-pc-windows-msvc/
          {name}.dll
```

### `versions.json`

Lists available versions for a package:

```json
{
  "versions": ["0.1.0", "0.2.0", "0.2.1", "1.0.0", "1.0.1"],
  "latest": "1.0.1"
}
```

### Package `cranelisp.toml`

Each version's `cranelisp.toml` describes the package:

```toml
[project]
name = "collections-extra"
version = "0.2.1"
description = "Additional collection types for cranelisp"
entry = "collections-extra.cl"

search-path = []    # packages should not declare external search paths

[deps]
# transitive dependencies with version constraints
core-utils = "^1.0"
```

A package's `search-path` is **not** used by consuming projects — only the root project's search path is authoritative. The package's `[deps]` section declares transitive dependency version constraints that are merged during resolution.

### Fetch Protocol

When a web URL entry on the search path is consulted for module name `foo`:

1. `GET {url}/foo/versions.json` — discover available versions
2. Apply version constraint from root project's `[deps]` (or lockfile pin, or latest)
3. `GET {url}/foo/{version}/cranelisp.toml` — read package metadata and transitive deps
4. `GET {url}/foo/{version}/archive.tar.gz` — download package source

Step 4 fetches the entire package as an archive. The archive is unpacked into the source cache and treated as a local directory for subsequent resolution.

### Design Decisions

- **No authentication in v1.** Public repositories only. Private repos via HTTP auth (bearer token, `.netrc`) planned for later.
- **No package signing in v1.** Source hashes in the lockfile provide integrity against corruption and tampering after initial fetch. Signing can be layered on.
- **No central registry required.** Any HTTP file server with the right layout works. A default public registry (e.g. `https://packages.cranelisp.org/`) can be established as a convenience.

## 6. Module Versioning

### Semantic Versioning

Packages use `major.minor.patch` versioning:

| Component | Change type | Example |
|-----------|-------------|---------|
| `major` | Breaking — removed exports, changed type signatures | `1.0.0` → `2.0.0` |
| `minor` | Additive — new public functions, new modules | `1.0.0` → `1.1.0` |
| `patch` | Bug fix — behavior changes within existing signatures | `1.0.0` → `1.0.1` |

### Version Constraints

Constraints in the `[deps]` section:

| Syntax | Meaning | Example range |
|--------|---------|---------------|
| `"1.2.3"` | Exact version | `= 1.2.3` |
| `"^1.2"` | Compatible range (default) | `>= 1.2.0, < 2.0.0` |
| `"^0.2"` | Pre-1.0 compatible | `>= 0.2.0, < 0.3.0` |
| `">=1.0, <3.0"` | Explicit range | `>= 1.0.0, < 3.0.0` |

A bare version string like `"1.2"` is shorthand for `"^1.2"` (caret/compatible range). This follows Cargo's convention.

### Resolution Algorithm

**Minimal version selection** (Go's approach): given constraints, pick the *lowest* version that satisfies all requirements. This is simpler and more predictable than maximal resolution — adding a new dependency cannot silently upgrade an existing one.

### Pre-release Versions

`1.0.0-alpha.1` syntax. Pre-release versions:

- Sort before their release: `1.0.0-alpha < 1.0.0-beta < 1.0.0`
- Are excluded from range matching unless explicitly requested
- Can be pinned with exact version syntax: `"1.0.0-alpha.1"`

### Type System Interaction

Cranelisp's type system provides a natural definition of "breaking change": any change to a public function's type scheme, a public type's constructors, or a public trait's method signatures. A future `cranelisp check-semver` tool could compare two versions of a package and detect breaking type changes automatically (analogous to `cargo-semver-checks` in the Rust ecosystem).

## 7. Manifest and Lockfile

### Two Files

| File | Edited by | Committed | Purpose |
|------|-----------|-----------|---------|
| `cranelisp.toml` | Developer | Yes | Declares project config, search path, version constraints |
| `cranelisp.lock` | Tool | Yes | Pins exact resolved versions + source hashes |

### Lockfile Format

```toml
# Auto-generated by cranelisp. Do not hand-edit.
# cranelisp 0.1.0, lock format 1

[[package]]
name = "collections-extra"
source = "https://packages.cranelisp.org/collections-extra"
version = "0.2.1"
source-hash = "sha256:a1b2c3d4e5f6..."

[[package]]
name = "core-utils"
source = "https://packages.cranelisp.org/core-utils"
version = "1.0.3"
source-hash = "sha256:f6e5d4c3b2a1..."

[[package]]
name = "stdlib"
source = "$CRANELISP_LIB"
source-hash = "sha256:1234abcd5678..."
```

Every package that was actually imported (directly or transitively) gets an entry. Local path packages are included with their path as source.

### Lockfile Lifecycle

| Command | Action |
|---------|--------|
| `cranelisp lock` | Resolve all search-path packages and write `cranelisp.lock` |
| `cranelisp update [name]` | Re-resolve one or all packages within `[deps]` constraints |
| (automatic) | If `cranelisp.toml` exists but `cranelisp.lock` does not, generate it before building |

**Stale detection:** if `cranelisp.toml` has been modified since the lockfile was last written (deps changed, search path changed), the compiler warns and suggests `cranelisp lock`.

### What Gets Locked

- Resolved version for each package (direct and transitive)
- SHA-256 hash of the package source (entire archive or per-file manifest)
- Source location (URL, path, or environment variable reference)
- The lockfile itself does not lock the compiler version — that's tracked separately by the cache manifest

### Lockfile and Cache Interaction

The project's `.cranelisp-cache/manifest.json` gains a `lockfile_hash` field. When the lockfile changes (a dependency was updated), the cache is invalidated for modules that import from changed dependencies.

## 8. Feature Flags

Feature flags enable conditional compilation — a package can expose optional functionality that consuming projects opt into.

### Declaration

In a package's `cranelisp.toml`:

```toml
[features]
default = ["json"]
json = []
xml = []
full = ["json", "xml"]
```

- `default` — features enabled when no explicit selection is made
- Named features — each is a list of other features it implies (dependency features)

### Consuming Features

In the root project's `[deps]`:

```toml
[deps]
serializer = { version = "^1.0", features = ["json", "xml"] }
```

Or to disable defaults:

```toml
[deps]
serializer = { version = "^1.0", default-features = false, features = ["xml"] }
```

### Semantics

Feature flags are a **build-time concept** — they control which modules are included in the compilation:

- A feature-gated module is declared with `(mod name)` but only compiled and linked when the corresponding feature is active
- Feature detection is **not** a language-level concept — there is no `(if-feature ...)` conditional in source code
- Features propagate through transitive dependencies: if package A enables feature `json` in package B, and B's `json` feature requires `core-json`, then `core-json` is included

### Open Design Questions

Feature flags interact with the type system in ways that need careful thought:

- If a feature adds a trait impl, does removing the feature constitute a breaking change?
- Should feature-gated modules be type-checked even when disabled (to catch latent errors)?
- How do features interact with the lockfile (different feature sets → different dependency graphs)?

This section may be partially deferred to implementation experience.

## 9. Interaction with Existing Systems

### Module Resolution (`src/module.rs`)

- `resolve_module()` replaces step 4 (lib dir heuristic) with a search-path walk when `cranelisp.toml` is present
- `find_lib_dir()` is only called when no TOML file exists (backward compatibility)
- `ModuleGraph::build()` loads `cranelisp.toml` at the start and constructs the search path object
- A new `SearchPath` struct encapsulates the ordered resolution logic

### Platform Resolution (`src/platform.rs`)

- `resolve_platform_path()` is replaced by the same search-path walk when TOML is present
- Each search-path directory is checked for `platforms/{triple}/{name}.{ext}`
- The target triple is determined at startup (matching the existing `target_triple` in the cache manifest)
- Without TOML, the current ad-hoc platform search is unchanged

### Cache (`src/cache.rs`)

- All compilation artifacts go into the project's `.cranelisp-cache/`, even for remote dependencies (compute is cheap)
- Remote source files are cached in `~/.cranelisp/source-cache/{url-hash}/{package}/{version}/`
- The cache manifest gains a `lockfile_hash` field to invalidate when dependencies change
- Dependency source caches are immutable — the same URL + version + hash is never re-fetched

### CLI (`src/main.rs`)

New subcommands:

| Command | Action |
|---------|--------|
| `cranelisp init` | Create `cranelisp.toml` in current directory with defaults |
| `cranelisp lock` | Resolve dependencies and write `cranelisp.lock` |
| `cranelisp update [name]` | Re-resolve one or all dependencies within constraints |
| `cranelisp fetch` | Download all remote dependencies to source cache |

Existing modes (`--run`, `--exe`, bare REPL) are unchanged. When `cranelisp.toml` is present, they use the configured entry point and search path.

### REPL

- Search path is used for `/mod` module loading and `(import ...)` resolution
- The REPL displays the source of resolved modules (local vs remote) in `/info` output
- `(platform ...)` declarations resolve via the search path

### Standalone Executable (`cranelisp-exe-bundle`)

- `--exe` includes dependency `.o` files from the project cache
- Platform DLLs from dependencies must be distributed alongside the executable, or statically linked if the platform crate supports it
- The lockfile ensures the same dependency versions are used for exe building as for development

## 10. Comparison

| Feature | Cargo (Rust) | deps.edn (Clojure) | go.mod (Go) | cranelisp |
|---------|-------------|--------------------|--------------|--------------------|
| Config file | `Cargo.toml` | `deps.edn` | `go.mod` | `cranelisp.toml` |
| Lockfile | `Cargo.lock` | none | `go.sum` | `cranelisp.lock` |
| Package identity | Registry name | Maven coordinates | Module URL path | Name on search path |
| Central registry | crates.io (required) | Clojars + Maven | proxy.golang.org (optional) | None required |
| Version resolution | Maximal compatible | Explicit | Minimal | Minimal |
| Native code handling | Build scripts, proc-macros | JNI, interop | CGo | Platforms (DLLs) |
| Native code trust | Auditable via crates.io | Maven trust model | Go module proxy | Search path priority |
| Feature flags | Yes (Cargo features) | No | Build tags | Yes |
| Unified search | N/A (one registry) | Multiple repos | One proxy chain | Unified path (modules + platforms) |

**Key differentiators:**

- **Unified search path for modules and platforms** — no other language treats native extension discovery and module discovery as the same operation.
- **Security-motivated ordering** — the search path is a trust hierarchy. Project-local code always takes priority over remote code. This is especially important for platforms (native code).
- **Search path resolves, deps constrain** — separation of "where to look" from "what versions to accept" is unusual. Most systems combine these into a single dependency declaration.

## 11. Implementation Plan

Incremental phases, each independently useful:

### Phase 0: TOML Parsing

- Add `toml` crate dependency
- Parse `cranelisp.toml` from project root (if present)
- Read `[project]` section; use `entry` for batch mode entry point
- No search-path changes yet — just read and validate the config
- **New file**: `src/project.rs`
- **Modified**: `src/main.rs`, `src/batch.rs`

### Phase 1: Local Search Path

- Read `search-path` from TOML
- Implement `SearchPath` struct with ordered local + env-var resolution
- Replace `find_lib_dir()` and `resolve_platform_path()` when TOML present
- Local path dependencies work at this phase
- **Modified**: `src/module.rs`, `src/platform.rs`

### Phase 2: Lockfile

- `cranelisp lock` resolves local-path packages and writes `cranelisp.lock`
- Source hash computation and verification
- Stale lockfile detection
- **New file**: `src/lock.rs`
- **Modified**: `src/main.rs`

### Phase 3: HTTP Fetch

- Add HTTP client dependency (`ureq` for minimal footprint)
- Implement `fetch_package(url, name, version)` with source cache
- `cranelisp fetch` command
- Web URL entries in search path become functional
- **New file**: `src/fetch.rs`
- **Modified**: `src/module.rs`, `src/project.rs`

### Phase 4: Version Resolution

- Semver parsing and constraint matching
- Minimal version selection algorithm
- Transitive dependency resolution
- **New file**: `src/semver.rs`
- **Modified**: `src/lock.rs`, `src/fetch.rs`

### Phase 5: Feature Flags

- `[features]` section parsing
- Feature-gated module inclusion/exclusion
- Feature propagation through transitive deps
- **Modified**: `src/project.rs`, `src/module.rs`

### Phase 6: Publishing

- `cranelisp publish` — package a project as a repository-ready archive
- Generate `versions.json` entries
- Validate package structure
- **New file**: `src/publish.rs`

## 12. Open Questions

| Question | Context |
|----------|---------|
| **Diamond dependencies** | If A depends on B and C, and both depend on D at incompatible major versions, what happens? Options: error (simplest), or allow multiple major versions (like Go). |
| **Source vs binary distribution** | Should packages distribute compiled `.o` files for faster builds? Source-only is simpler, portable, and sufficient for v1. Binary caching is a local concern (project `.cranelisp-cache/`). |
| **Workspace/monorepo support** | Should `cranelisp.toml` support multiple packages in one repository? Not needed for v1 but should not be precluded. |
| **Private repositories** | HTTP authentication (bearer tokens, `.netrc`, SSH). Not in v1 but the URL-based model supports it naturally. |
| **Standard library versioning** | Is the stdlib versioned independently of the compiler? Currently tied to the compiler binary. Decoupling adds complexity. |
| **REPL dynamic deps** | Can the REPL add search-path entries or deps at runtime? Or is `cranelisp.toml` batch-mode only? |
| **Name collision** | If a project file `foo.cl` exists AND a package `foo` exists on the search path, project wins (steps 1-3 before step 4). Is this always correct? Should it warn? |
| **Transitive search paths** | A dep's `cranelisp.toml` may have its own `search-path`. Should it be honoured? Proposed: no — only the root project's search path is authoritative. Transitive deps declare `[deps]` constraints, not search locations. |
| **Package name discovery** | How does a search-path directory or URL advertise which packages it contains? For local paths, directory listing. For URLs, an optional `index.json` or per-package `versions.json` probing. |
| **Feature flag type safety** | If enabling/disabling a feature changes the set of available types or trait impls, this affects type checking. Need careful design of the interaction. |
| **Publishing workflow** | Manual directory creation, or a `cranelisp publish` tool? How are package archives signed? Who maintains `versions.json`? |
| **Platform target triples** | Convention: `platforms/{triple}/{name}.{ext}`. Should there be a fallback for "any platform" DLLs? What about cross-compilation? |
