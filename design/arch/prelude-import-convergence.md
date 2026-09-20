# Prelude and explicit imports — one resolution

Current architecture contract owned by `arch`. It states how a name reaches
its declaration identically whether the prelude, an explicit import, a
re-export or the module itself provides it, and what REPL introspection owes
that resolution. Exact signatures and refusals live in
[the resolver rustdoc](../../crates/cranelisp-types/src/resolve.rs); candidate
storage is [the symbol-table lifecycle](symbol-table-lifecycle.md#3-resolution-and-canonical-bindings);
the display and enumeration side of the same defect family is
[resolve home before enumeration](resolve-home-enumeration.md). Current evidence
navigation is [prelude and explicit-import parity](../../tests/plan/PLAN.md#prelude-and-explicit-import-parity).
The S108 variant census, collapse map, blast-radius scout and implementation
plan are delivery history in Git.

## 1. The settled model (spec-grounded; not open)

[The module specification](../../spec/08-modules.md) §8.6.4, §8.6.5 and §8.8.1
govern; this contract adds no language rule.

- The implicit prelude is `(import [prelude [*]])`. A prelude-provided name is
  in a module's scope on the same terms as an explicit import.
- Storing prelude names outside a module's own table is a storage choice with
  no semantic weight. There is no "outer scope" language concept. Documents,
  rustdoc and memories say **prelude fallback** for the mechanism and never
  describe it as a scoping level with its own rules.
- One spelling may denote several canonical declarations: a local declaration,
  imports, re-exports, prelude names and derived members. Paths reaching one
  terminal identity deduplicate; distinct terminals remain candidates, and none
  takes precedence by origin, visibility, import shape or arrival order. A use
  is valid when ordinary context leaves exactly one.
- Only `let`, `fn` and `match` bindings shadow, and they shadow the whole
  module-scope set.
- A module that names `prelude` in an `import` or `export` form receives no
  implicit prelude.

This supersedes the S108 reading under which a definition over any in-scope
name was a compile-time conflict; see [§4](#4-definitions-register-candidates).

## 2. The class this prevents

One semantic operation — resolve `name` from module `M` — was once implemented
as a family of per-site variants, each deciding for itself whether to consult
the prelude. Every new resolution site could forget it, and several did. The
cure is structural: the forgettable decision is not available at a call site.
[The review memory](../review/CLAUDE.md) carries the per-diff cue for divergent
and entry-point duplication.

## 3. The one lookup: `ResolutionScope`

The prelude fallback is a property of the resolution scope, decided once at
construction. Types exposes no resolution entry that takes a per-call fallback
flag and no fallback-less entry. A caller that must not fall back constructs a
scope with `prelude: None`, which is one explicit, reviewable decision.

### 3.1 Shape and home

`ResolutionScope` lives in `cranelisp-types` because it is a query over
types-owned data with two consumers, typecheck and the binary, that must not
depend on each other ([Principle 15](principles/15-facade-types-live-with-behavior.md)).

- `resolve_candidates` returns every terminal declaration the spelling exposes.
  For an unqualified name it unions the caller's first-hop view of the current
  module with the prelude's **public** candidates when the scope has a prelude,
  deduplicating by canonical identity. The union is unconditional; it is not a
  retry after an inner miss.
- `resolve` succeeds when that set has exactly one member and otherwise returns
  `ResolveError::Ambiguous` listing the canonical alternatives.
- `resolve_macro_head` projects the candidates that are macros, because macro
  recognition precedes type inference and cannot be selected by it.
- A qualified `mod/sym` applies the scoped module-alias walk and never consults
  the prelude; it names its module. Across a module boundary only public
  exposures participate.
- `Resolved` carries the terminal binding and its one canonical storage
  identity. Candidates name their terminals directly, so resolution follows no
  import chain.
- The caller chooses the first-hop view: committed tables for macro
  recognition, staging over live for typecheck. Terminals in other modules are
  read from committed tables.

Typecheck owns selection among several viable candidates under §8.6.5; types
performs scope, qualification and visibility work only.

### 3.2 Scope constructors

One seam per consumer reads the `prelude_fallback` bit and builds the scope:

- **typecheck** — `TypeCheckEnv::with_scope`, behind `scope_resolve`,
  `scope_resolve_candidates` and their `_in` forms for an arbitrary root
  module. `prelude_fallback_target` is its private bit read.
- **binary** — `recognize_macro_head` in
  [the expander](../../src/expander.rs), over the committed view.

REPL introspection is the binary's other reader of the committed view
([§3.5](#35-repl-introspection)).

### 3.3 The only fallback-less probe

The idempotent re-registration check asks whether this module already carries
this exact declaration. It is a raw current-module read
(`probe_module_entry_owned`), named as a probe. It answers same-module identity
and must never be reachable under a name that reads as reference resolution.

### 3.4 Fate of the `prelude_fallback` bit

The bit stays. It is the per-module fact "this module receives the implicit
prelude": role data under [Principle 19](principles/19-no-module-privileged-by-name.md),
session-side, unserialized and recomputed per session. Absence means off.

Two sites write it, both maintaining that one invariant:

- `ensure_prelude_bit` in [cluster dependency handling](../../src/process_form/dependency.rs),
  for fresh and incremental cluster processing. `inject_prelude_if_needed`
  only loads the prelude so the fallback has a table to consult.
- `install_module_session_env` in [import installation](../../src/imports.rs),
  for cache restoration and session-environment reinstall.

Reads belong to the scope constructors of §3.2 and to readers that need the
fact itself rather than a resolution: the REPL tier walk (§3.5),
`prelude_implicit_names`, the type-side implementation view and the index
feeds ([resolve home before enumeration](resolve-home-enumeration.md)), and
typecheck's `find_trait_method_decl`, a method-name-to-trait enumeration that
`resolve` cannot answer. Each prelude-side read keeps public names only. A new
reader outside these classes is a review finding.
[Prelude table write isolation](../int/prelude-table-write-isolation.md) owns
the binary-side writer discipline.

### 3.5 REPL introspection

REPL introspection — bare lookup, `/sig`, `/info` and `/doc` — enumerates a
spelling's candidates; it never selects among them.
[The multi-candidate display rule](../../repl/spec/04-self-documentation.md#4111-spellings-with-several-candidates)
and [the `/sig` rule](../../repl/spec/03-slash-commands.md) §3.8 govern: every
in-scope canonical candidate is reported, each under its fully-qualified name,
with no ambiguity error or warning and no comparison of candidate types. A
*use* of the spelling still resolves under §8.6.5 unchanged. Whether an import
may introduce a conflicting name at all is deferred to
[ACT-0961](../../sprints/actions/ACT-0961-revisit-conflicting-import-rule.md);
this contract takes no position on it.

Obligations to resolution:

- **One candidate set.** The set introspection reports for a spelling asked
  from module `M` is the set `resolve_candidates` returns for it: the same
  first-hop and public-prelude union, terminal deduplication, scoped alias walk
  for a qualified name and cross-module visibility. A private prelude name is
  in no module's scope (§8.8.1), so introspection never reports one.
  Introspection reads that set from the types primitive over the committed
  view; a display-side mirror of the walk is the class §2 forbids. The listing
  is [Principle 24](principles/24-resolve-once.md)'s complete-set enumeration.
- **No selection at introspection.** `resolve` and `resolve_macro_head` are the
  only entries that report `ResolveError::Ambiguous`; they serve uses.
  Introspection calls neither for a displayed name, so the required silence is
  a property of which entry it reads.
- **Canonical-home rendering.** Each candidate renders from its own
  `Resolved::canonical`: that key supplies the fully-qualified name, and its
  module is the home every section lookup roots at
  ([resolve home before enumeration](resolve-home-enumeration.md#3-the-rule)).
  A displayed identity is never derived again from the bare spelling.
- **The root `""` tier is not a candidate source.** Special-form metadata lives
  in the root module, which reference resolution never consults. Introspection
  reads it only for a spelling whose candidate set is empty.

[The int design](../int/int.md#33-repl-commanddisplay-surface-srcrepl) owns the
query, its result representation, candidate ordering and the per-command
rendering.

**Separate question: scope membership.** `/search`'s in-scope mark,
`symbol_is_bound` and the agent harvest's mentionable check ask only whether a
spelling is in scope, through the tier-first helper `lookup_with_prelude_fallback`. They are outside the display
rule; their disposition is
[the int design's recorded residual](../int/int.md#33-repl-commanddisplay-surface-srcrepl).
The private-prelude exclusion above binds them equally.

## 4. Definitions register candidates

Spec §8.6.4 makes a module-local declaration over an imported, re-exported or
prelude-provided spelling legal: it registers another candidate. The S108
ruling that routed every definition form through one rejecting seam
(`reject_def_over_binding` over `check_binding_addition`) is therefore
withdrawn, and neither function is part of the types public surface.

What remains of that ruling:

- Definition forms behave identically in every compilation mode, because they
  write candidates through the one table mechanism and resolution is
  use-site.
- Module-routing names are not candidate sets. Colliding import aliases, export
  mounts, or a mount over a real submodule remain compile-time errors (§8.3.4,
  §8.4.4).
- Repeated declaration legality is governed per declaration category by the
  specification, not by import provenance.

## 5. Public surface and cache

- The types surface for this contract is `ResolutionScope` (`new`, `resolve`,
  `resolve_candidates`, `resolve_macro_head`), `Resolved`, `ResolveError`,
  `NameCandidate` and `substitute_module_alias`.
  [The generated baseline](../../crates/cranelisp-types/public-api.txt) is the
  surface evidence; this document approves no change to it.
- No serialized type depends on this contract. The scope is a borrowing view,
  the bit is unserialized, and resolution results are not cached.
