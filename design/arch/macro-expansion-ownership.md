# Macro expansion ownership

**Status.** Adopted cross-context contract, landed (S76 W-Macro; checkpoint
amendment 2026-09-03). Owner `arch`. This document states which context owns
each half of macro expansion and why the split is shaped as it is. *When* a
macro is available and the source-ordered checkpoint sequencing are the
[macro availability model](macro-availability-model.md); the binary's
expansion-loop interior is
[macro resolver implementation](../int/macro-resolver-impl.md) and
[quote shield](../int/int.md#66-pass-1-quote-shield); the boundary type is
`cranelisp_types::MacroExpander` and its rustdoc.

## 1. The split

Macro expansion is two jobs with one seam between them.

| Job | Needs | Owner |
|---|---|---|
| **Recognise** — is this head a macro, and which canonical `FQSymbol`? | Symbol-table lookup over committed tables, import and alias walk, prelude fallback | `cranelisp-types` query (`ResolutionScope::resolve_macro_head`), called by the binary |
| **Execute** — turn (macro identity, argument `Sexp`s, call span) into one output `Sexp` | The compiled clause's GOT address, `Sexp`↔heap marshalling, the runtime panic slot, `sigsetjmp`/`siglongjmp` | The binary, behind `cranelisp_types::MacroExpander` |

The two jobs communicate through exactly two values: **down** = (identity,
argument `Sexp`s, call span); **up** = the output `Sexp`. Neither carries a type
that inverts the dependency graph.

**Where the walk runs.** The binary's Pass-1 expand loop
(`src/expander.rs::expand_sexp_recursive`, driven from
`process_form::process_cluster_once` through
`process_form/macro_resolution.rs`) walks each form, recognises heads, executes
committed clauses through its own `MacroExpander` implementation, rebuilds the
result and re-enters to fixpoint — nested macros and structural results
(`(begin (defn …) (defmacro …))`) alike. The expansion depth bound lives in that
loop. Only when no macro head remains does one `check_forms` call receive the
fully expanded non-macro `ParsedEntry` list. Each direct or expansion-produced
`defmacro` is prepared, checked, compiled and published as one module-local
checkpoint inside the same loop, before later forms expand
([availability model](macro-availability-model.md) §3, §5).

### Per-context obligations

- **Frontend** — syntactic only: `parse`, quasiquote desugaring
  (`expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`) and
  `Sexp` → AST building (`build_form`, `build_forms`,
  `synthesize_macro_clause_defn`). It consults no symbol table, recognises no
  macro head and calls no compiled clause (BC §1 invariant 2). There is no
  frontend `expand` entry and no frontend expansion error type.
- **Types** — owns the recognition query and the execution callback type.
  `MacroExpander` / `MacroInvokeError` live here because the callback crosses
  the binary boundary and adds no dependency edge; `resolve_macro_head` is the
  typed macro projection of the one resolution query (BC §7).
- **Typecheck** — receives fully expanded non-macro forms and never sees a
  macro invocation. Its only macro-adjacent work is checking a `defmacro`'s
  synthesised clause definitions as ordinary `defn`s when the binary prepares a
  checkpoint. It holds no `MacroExpander` and calls no recogniser: the
  `check_forms` frame is a pure two-pass over already-expanded entries, which
  is what keeps its cluster commit atomic (BC §2 invariant 11).
- **Binary** — implements `MacroExpander` over its invocation core
  (`JitMacroExpander`: clause selection, marshal, signal-protected call,
  unmarshal, fresh synthetic spans), owns the expand loop, the quote shield,
  the qualification walk and checkpoint publication (BC §6).

## 2. The callback boundary

`MacroExpander::invoke(&self, fq, args, call_span) -> Result<Sexp, MacroInvokeError>`,
`Send + Sync`; `MacroInvokeError` is `#[non_exhaustive]` with `Aborted` and
`Malformed` arms. Exact obligations are the trait's rustdoc.

- **A trait object, not a fn handle.** The implementor holds session state (the
  committed tables it reads clause pointers from, per-call thread-local signal
  buffers). `&dyn MacroExpander` carries that behind one named contract with a
  named error shape; a bare `fn` or `&dyn Fn` is the same vtable with a less
  legible signature (Principle 2).
- **The result is a raw `Sexp`.** A classified return (`Vec<ParsedEntry>`, or
  an expression-versus-structural enum) would make the execution side know
  about form classification, carry a parse-time transient across the boundary
  as a return, and duplicate the re-walk the loop must do anyway because a
  result may contain further macro calls at any depth. The executor does one
  thing: (identity, args) → one `Sexp`.
- **`Send + Sync`** because workers may expand concurrently; the invocation
  core isolates per-call signal state in thread-locals.
- **No new crate.** A `cranelisp-marshal` bridge crate was rejected by the user
  (S76): it would re-export the allocator and signal machinery across a
  types-stable surface. The callback achieves the separation with no new crate
  and no dependency widening of frontend or typecheck.

Dependency graph, unchanged and acyclic: frontend, typecheck and the binary each
depend on types; the binary depends on typecheck; the only new flow is a value
the binary constructs and consumes itself.

## 3. Why the loop is the binary's, not `check_forms`'

The first S76 design pass left open whether the `Sexp` walk should run inside
`check_forms` (typecheck re-classifying structural results against its staging)
or in the binary before it. The user locked the second shape on 2026-06-03
([availability model](macro-availability-model.md) §4, §5). The reasons
still bind:

- **No frontend dependency in typecheck.** Rebuilding an expansion result into
  `ParsedEntry`s needs `build_form`; typecheck depends only on types (BC §2).
  Running the loop in the binary keeps `build_form` where it may be called.
- **Cluster atomicity stays a true statement.** `check_forms` registers
  signatures and checks bodies in one frame against orchestrator-owned staging,
  committed atomically. A macro invocation inside that frame would need a
  committed clause mid-cluster; keeping expansion outside it, over committed
  clauses only, leaves the non-macro commit untouched (Decision 44, BC §2
  invariant 2).
- **Same-module non-macro definitions are unavailable at expansion.** A clause
  may call dependency-module definitions and same-module macros, never a
  same-module `defn`. This removes the case (an empty GOT slot for an
  uncompiled same-module helper) that the S76 concrete trace found rather than
  patching it with a pre-invocation callee compile; the dead
  `block_for_macro_codegen` path was deleted, not wired
  ([availability model](macro-availability-model.md) §2).
- **One walk.** The frontend's structural-walk skeleton was deleted rather than
  kept private: two implementations of the same walk in two crates is a
  Principle 7 drift source. The bare-name "probe every module" lookup it
  carried was replaced by the current-module-view query (Principle 17).

## 4. Where the contract manifests

| Carrier | Content |
|---|---|
| `crates/cranelisp-types/src/macro_expander.rs` | `MacroExpander`, `MacroInvokeError` and the boundary rustdoc |
| `crates/cranelisp-types/src/resolve.rs` | `ResolutionScope::resolve_macro_head` |
| `src/expander.rs`, `src/process_form/macro_resolution.rs`, `src/process_form/macro_clause.rs` | The expand loop, recognition wrapper with prelude fallback, `JitMacroExpander`, checkpoint preparation |
| [Bounded contexts](bounded-contexts.md) §1, §2, §6, §7 | Per-context statements and invariants |
| [Boundary types](interfaces.md) §Macro execution callback | Narrative companion to the trait |
| [Compilation sequence](sequences/exec-flow-compilation.mmd) | The three-pass model with Pass 1 in the binary |
| `src/CLAUDE.md` §Macro expansion | Binary-side conventions: single executor, quote shield, qualification walk |

## 5. Retired section remaps

Earlier revisions of this document carried the S76 deliberation. For readers
holding an old citation:

| Old section | Now |
|---|---|
| §1 The decision; §2 Two jobs; §2.1 Frontend; §2.2 Typecheck | §1 |
| §2.3 Int after the split — execute via the injected callback | §1 "Binary" and §2 |
| §3 The callback boundary type | §2 |
| §4, §4.1, §4.2 structural re-entry; §4.3 the build_form subtlety and its pinned decision; the withdrawn §4.4 callee-codegen step | §3 |
| §5 cascade map | §4 (current carriers; the migration rows are Git history) |
