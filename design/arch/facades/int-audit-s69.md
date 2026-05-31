# int — Sprint 69 facade audit (re-authored against the architectural configuration)

> **Naming note (facade-coherence pass, post-S72).** The boundary type `ClusterContext` is renamed `SymbolTableAccess` — every `ClusterContext` mention below reads as `SymbolTableAccess` (the `Live` / `Cluster` variant names are unchanged). See `facades/typecheck.md` §"Cluster check scaffolding" naming rationale.

**Owner**: `/design (int)`
**Scope**: `src/` (binary crate — no `public-api.txt`; audited via direct source read) + `crates/cranelisp-exe-bundle/` (11-line `public-api.txt` + 101-line `lib.rs`).
**Audit-as-of**: 2026-05-19 (re-author).

**Why re-authored.** The prior version of this file (2026-05-19, same date) dispositioned 21 findings without first loading the architectural configuration that *grounds* the facade. Per user direction:

> "the issue is that the audit did not read the architectural configuration and derived design docs."

A facade is a contract surface; its **meaning** lives in the Decision register, the Principles, the bounded-context statements, the sequence diagrams, and the open FIXMEs. An audit that reads only facade + `lib.rs` + the source method bodies sees the lexical difference between the two sides, but has no grounding for which side carries the intent — and so it disposes drift by "whichever side is currently settled wins," which is the regression mechanism documented in `memory/feedback_audit_per_item_analysis.md`. The default disposition for a target-stating facade item absent from source is **source moves**, because the facade IS the binding intent. The default for a facade item that a later Decision retracted is **facade moves**. Without the Decision register loaded, the two cases are indistinguishable.

**Configuration loaded for this re-author**: `design/arch/principles.md` + every `principles/*.md` (notably 07 single-source-of-truth, 13 `interfaces.md`-is-auditable, 17 module-locality, 18 enforce-structurally); `design/arch/CLAUDE.md` (active Decisions index + baseline-diff discipline); `bounded-contexts.md` §6 (int BC); every active Decision (esp. 0030, 0031, 0035, 0040, 0041, 0043, 0044, 0048); legacy Decisions referenced (esp. 0021, 0023, 0033, 0036–0039 via the CLAUDE.md index narrative); `sequences/exec-flow-compilation.mmd`, `exec-flow-repl.mmd`, `exec-flow-link.mmd`, `concurrency-symbol-table-entry.mmd`; the int facade `design/arch/facades/int.md` (1377 lines, full); `design/int/*.md`; `src/CLAUDE.md`; `design/arch/fixmes/0179`, `0194`, `0214` (and the related cluster `0167`, `0168`, `0176`).

**Discipline.** Per `memory/feedback_audit_per_item_analysis.md`: every finding gets a five-block analysis — **What the facade expects / What the source does / What is the design intent (grounding citation) / What the difference implies / Disposition (binary choice + evidence + grounding-traceable rationale)**. Deferral is acceptable only AFTER the disposition is named — schedule, not avoidance. "Defer to S70 via FIXME" is a scheduling statement; it does not substitute for the disposition.

The companion `design/arch/facades/types-audit-s69.md` is the shape exemplar.

---

## Findings

### Finding F-1 — `pub fn format_command_result(&self, result: &CommandResult) -> String` is absent from source

**Facade expects:**
> `pub fn format_command_result(&self, result: &CommandResult) -> String;` (facade L102, in the `impl CompilerSession` "REPL display + IO" block).

**Source does:**
No such method exists on `CompilerSession`. `main.rs:237-243` consumes `CommandResult` directly via per-variant match: `CommandResult::Final(text)` flows to `s.pretty_print(&text, &mut stdout)`; `CommandResult::Compile(src)` flows into `s.eval(&src)` and the result goes through `s.format_eval_result(&result)` (which DOES exist at `session_v4.rs:4093`); `CommandResult::Nothing` / `CommandResult::Quit` are not displayed. No central `format_command_result` formatter exists or is called.

**Design intent:**
The facade comment beside this method names no companion to `format_eval_result`; it is a symmetric naming gesture (one formatter per result type) consistent with `repl/spec.md` §15 self-documenting REPL. No Decision pins the centralisation; no FIXME tracks source-side authoring. The per-handler-already-formatted-text design (each slash-command handler in `session_v4.rs:2331-2424` returns `CommandResult::Final(already_formatted)`) is the source-side precedent, and no Decision retracted it. The facade row is **target-stating-by-symmetry**, not target-stating-by-Decision. Principle 7 (single source of truth) speaks weakly here — there IS no duplicated logic, because the per-handler text IS the source of truth for that handler's output. A central formatter would be a thin dispatch on variant: `match result { Final(t) => t.clone(), Compile(_) => unreachable, ... }` — adding it would not consolidate existing duplication, because there is no duplication.

**Difference implies:**
A reader of the facade follows a method that does not exist. The actual display path is decentralised. Downstream consumers writing alternative drivers (test harnesses, alternate REPL hosts) must replicate `main.rs:237-243`'s per-variant match — but that match is 6 lines, and the variants are `#[non_exhaustive]`-stable per the facade.

**Disposition:**
**Facade moves — Wave 2 (facade-doc).** Remove `format_command_result` from facade L102. The decentralised shape is correct because there is no consolidation to centralise — each handler already produces the user-visible string, and `CommandResult::Final` wraps it. No Decision or Principle is violated by removal. The audit's prior disposition stands on this one (consistent with grounding); the re-author confirms it without flipping.

### Finding F-2 — `pub fn format_error(&self, error: &CranelispError) -> String` is absent from source

**Facade expects:**
> `pub fn format_error(&self, error: &CranelispError) -> String;` (facade L103, with the doc comment "resolves ErrorLocation + introspection.source for rich display").

**Source does:**
No `format_error` method on `CompilerSession`. `main.rs:90-114` defines a free function `fn format_error(err: &CranelispError, entry_file: &Path) -> String` that resolves `ErrorLocation` + reads the file from disk to derive line:col. It does NOT consult `shared.introspection`. It takes `&Path` (entry file fallback), not `&self`, so it has no access to session state.

**Design intent:**
The facade L103 comment is explicit: "resolves ErrorLocation + introspection.source for rich display." The grounding is Decision 0038 (legacy — `SharedState` formalisation; the worker-shareable subset includes `Introspection` per-symbol records) + Decision 0041 (per-symbol JIT cardinality; backend writes `introspection[fq].source/clif_ir/disasm/...` directly per-symbol). The introspection map is the canonical home for captured source slices (REPL mode + trace mode). `repl/spec.md` §3 self-documenting REPL design principle requires "no opaque error" — error display SHOULD quote the surrounding source for REPL evals (no on-disk file exists). The facade's `&self` binding is the structural seam that exposes `shared.introspection` to the formatter.

**Difference implies:**
The free function in `main.rs` falls back to reading the file from disk — works only when the file is on disk and unchanged; fails for REPL evals (no file); fails for changed files. A user-proxy skill (`/qa`, `/repl`) wanting to surface a richer error display (with source context from introspection) cannot call a session method; they must replicate file-reading logic. The richer-display intent named in the facade comment, grounded in Decisions 0038 + 0041 + `repl/spec.md` §3, is unmet.

**Disposition:**
**Source moves — Wave 3.** The facade target is the right shape: a `&self` method that consults `shared.introspection` is the load-bearing improvement, and the introspection map IS the binding source-of-truth for REPL-captured source (Principle 7). Implementation: read `loc.file` + `loc.line_col` (current behaviour); AND if `shared.introspection.get(&fq_at_loc).is_some()` prefer the captured source string for line:col derivation (cheaper + more reliable than file IO; handles REPL eval where no on-disk file exists). The current `main.rs::format_error` collapses into `CompilerSession::format_error` with the file-fallback retained for non-REPL paths. /dev (int) Wave 3.

The prior audit's disposition stands; the re-author confirms with explicit Decision-grounding (Decisions 0038 + 0041 + Principle 7 + `repl/spec.md` §3).

### Finding F-3 — `Reload(Option<ModuleFullPath>)` variant + the `SlashCommand` enum's public/private status

**Facade expects:**
> `pub enum SlashCommand { Help, List, Imports, Exports(ModuleFullPath), Sig(Symbol), Doc(Symbol), Type(Symbol), Info(Symbol), Source(Symbol), Sexp(Symbol), Ast(Symbol), Clif(Symbol), Disasm(Symbol), Time(Symbol), Mem, RunTests, Mod(Option<ModuleFullPath>), Reload(Option<ModuleFullPath>), Expand(String), Quit, /* … */ }` (facade L496-502).

**Source does:**
`enum ReplCommand<'a>` at `session_v4.rs:188` is **private** (no `pub`), lifetime-parameterised on `&'a str` (not the typed newtypes), with these variants per `parse_slash_command` at `session_v4.rs:286-308`: `Help, Quit, Sig(arg), Doc(arg), Type(arg), Info(arg), List(arg), Mem(arg), Time(arg), Expand(arg), Imports(arg), Exports(arg), Source(arg), SexpCmd(arg), Ast(arg), Clif(arg), Disasm(arg), Mod(arg), RunTests(arg), RunAllTests, Reset, Sh(arg), Unknown(&str)`.

Differences: no `Reload` variant (file-watcher reloads route through `poll_and_reload()` at `session_v4.rs:1710`); extra variants `RunAllTests`, `Reset`, `Sh`, `Unknown` in source; enum is private; payloads are `&'a str` not newtypes.

**Design intent:**
The facade names a public enum that does not exist as a public type. The grounding for the choice is Principle 13 (`interfaces.md` is auditable — every public type in the facade is part of the auditable contract surface) + Principle 02 (narrow interfaces — exposing an internal lifetime-keyed enum across a public boundary is not a narrow interface). The `&'a str` keying in source is bound to the input-line buffer lifetime — the enum cannot escape the parse-and-dispatch frame anyway, which is the structural reason source kept it private. **No Decision pins `SlashCommand` as public surface**; the facade naming is target-stating-by-symmetry-with-`CommandResult` (which IS public — see F-1) rather than by a Decision that says "the slash-command enum is part of int's API." The `Reload` variant naming is consistent with the facade's other module-action variants (`Mod`, `Exports`) but conflicts with the source design choice that file-watcher reloads route through `poll_and_reload()`, not through the slash-command parser.

**Difference implies:**
Anyone writing an alternate REPL host that imports `cranelisp::SlashCommand` finds it does not exist. The `&'a str` keying makes a public form unworkable without owning the data (requires `String`/`Symbol`/`ModuleFullPath` payloads). The `Reload` row in the facade either (a) commits to a new `/reload` slash command (does not exist today) or (b) is a documentary artefact that should not be there.

**Disposition:**
**Facade moves — Wave 2 (facade-doc).** Two valid binary choices, named:
- (a) Demote `SlashCommand` to a documentary descriptor — add a note that the actual implementation is a `pub(crate)`-private lifetime-keyed `ReplCommand<'a>` enum and that command dispatch is internal to `process_commands`. Drop `Reload` from the facade enum. Add `Sh`, `RunAllTests`, `Reset`, `Unknown` to the facade enum with documentary status.
- (b) Make source `ReplCommand` `pub`, own (`String`/`Option<ModuleFullPath>`/`Symbol`) payloads, rename to `SlashCommand`, add the `Reload` variant (which means authoring a `/reload` parse path that calls `re_register_module`).

(a) is the lower-churn correct answer under Principle 02 (narrow interfaces) + Principle 13 (every public type carries audit cost) — the slash-command surface IS internal; no consumer outside int needs to construct or pattern-match it. (b) would be a multi-day refactor with no consumer demanding it. Pick (a) for Wave 2 facade-doc. /dev Wave 3 may revisit (b) only if a downstream consumer materialises (recorded in arbitration A-2 below for /arch override).

Prior audit's disposition (a) stands; the re-author confirms it WITH Principle grounding (02, 13) rather than YAGNI hand-wave.

### Finding F-4 — `pub fn register_module(&mut self, module: &ModuleFullPath)` receiver type drift

**Facade expects:**
> `pub fn register_module(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError>;` (facade L42, with the comment "Phase 0 (parse + write_structural_decls) runs synchronously here, before dispatching PriorityWork::Typecheck").

**Source does:**
`pub fn register_module(&mut self, module_name: &str) -> Result<(), CranelispError>` at `session_v4.rs:2020-2026`. Argument type is `&str`, not `&ModuleFullPath`. Body: `self.register_entry_module(module_name)?; Ok(())`. The sole call site is `main.rs:172`: `s.register_module(entry_module_name)?;` where `entry_module_name: &str` is from CLI parse (post-`resolve_target`).

**Design intent:**
The facade conforms to the **hard rule** in `design/arch/CLAUDE.md` §"String Newtypes": "All identifier fields in boundary types MUST use the appropriate newtype, never bare `String`. This prevents accidental mixing of identifiers across semantic categories (e.g., passing a module path where a symbol name is expected)." `ModuleFullPath` is the canonical type for dotted module paths. The `&str` receiver in source admits a stringly-typed bare path that could be the wrong category (a `Symbol`, a file-path-portion, a `LinkerSymbol`); the compiler does not catch the mistake. This is the same axis as types-audit F-2 / F-5 (newtype discipline) and is grounded in Principle 18 (enforce architectural invariants structurally where possible) — the newtype IS the structural mechanism that prevents category-confusion, and abandoning it at a public-API boundary defeats the invariant.

**Difference implies:**
The newtype-at-boundary discipline is broken at one public method. The call site in `main.rs:172` is already constructed by `parse_args` from CLI input — it would trivially become `ModuleFullPath::from(entry_module_name)` at the call site (or, better, `resolve_target` returns a `ModuleFullPath` directly). No structural blocker.

**Disposition:**
**Source moves — Wave 3.** Trivial newtype narrowing. Change source signature to `&ModuleFullPath`; update `main.rs:172` to pass `&ModuleFullPath::from(entry_module_name)` (or pivot `resolve_target` to return the newtype). /dev (int) Wave 3 — folded into Wave 3 alignment commit. The hard-rule grounding (CLAUDE.md §"String Newtypes" + Principle 18) makes "source moves" the only valid disposition; "facade moves" would retreat from the project-wide newtype discipline.

The prior audit's disposition stands. **Re-author flip vs prior framing:** the prior audit named this as "trivial newtype narrowing" without citing the hard rule that makes it non-negotiable. Re-author confirms with grounding — this is not a stylistic preference, it is the project's structural invariant for boundary types.

### Finding F-5 — `regenerate_backing_file` signature drift (no module parameter; unit return)

**Facade expects:**
> `pub fn regenerate_backing_file(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError>;` (facade L111, with doc "iterates SymbolTable::defn_order, emits introspection[fq].source per entry — per repl/spec.md §15").

**Source does:**
`pub fn regenerate_backing_file(&mut self)` at `session_v4.rs:1802` — takes NO module argument, returns `()` (not `Result`). Body opens with `let module = self.current_module_path();` — always uses the current REPL module. Two call sites at `main.rs:255, 263` both call `s.regenerate_backing_file()` (no arg).

**Design intent:**
The facade prescribes a parameterised form callable for any module. The grounding: `repl/spec.md §15` "backing-file regeneration is per-module" + Principle 12 (design for full spec surface) — a method named `regenerate_backing_file` should accept the module to regenerate; hard-coding current-module is a hidden assumption that breaks the moment a second caller appears (file-watcher cascade target, tooling-level "regenerate ALL" sweep, the hypothetical `/reload` implementation under F-3 option b). The `Result` wrapper allows surfacing IO failures from `save.rs::atomic_write`; the unit-returning source swallows them at the IO layer — a Principle 06 (complexity budget) violation by inversion (error-handling complexity now lives in `save.rs` instead of at the API boundary).

**Difference implies:**
A future caller wanting to regenerate a module other than current REPL one has no way in. IO failures from `atomic_write` are invisible to the caller. Future broadening of regeneration scope (FIXME-implied; file-watcher cascade, `/reload` resolution) requires a signature change anyway.

**Disposition:**
**Source moves (partial) — Wave 3.** Two narrowings:
- Add `module: &ModuleFullPath` parameter. Callers at `main.rs:255, 263` pass `&s.current_repl_module().clone()` (or a borrow if lifetimes permit).
- Wrap return in `Result<(), CranelispError>` and propagate the `atomic_write` error.

Mid-priority. /dev (int) Wave 3. Prior disposition stands; re-author confirms grounded in `repl/spec.md §15` + Principle 12.

### Finding F-6 — `init_watcher` / `sync_watcher` return-type drift (Result vs unit)

**Facade expects:**
> `pub fn init_watcher(&mut self) -> Result<(), CranelispError>;` (facade L106)
> `pub fn sync_watcher(&mut self) -> Result<(), CranelispError>;` (facade L107)

**Source does:**
`pub fn init_watcher(&mut self)` at `session_v4.rs:1413` — returns `()`. Body: matches `FileWatcher::new()`, silently returns on `None`. Cannot fail.
`pub fn sync_watcher(&mut self)` at `session_v4.rs:1688` — returns `()`. Body: locks `file_to_module`, iterates, calls `watcher.watch_file(path)`. No fallible step.
`main.rs:208, 275` calls both without `?` — fits a unit-returning signature.

**Design intent:**
**No Decision pins a fallible signature** for either method. The facade's `Result<(), CranelispError>` is target-stating-by-symmetry-with-other-fallible-methods, NOT by a Decision that says "watcher initialisation can fail and the caller must observe it." `notify::Watcher::new()` is the underlying primitive and is infallible-by-design under the source's wrapper (returns `None` → silently absent). A future change to surface "watcher initialisation failed" as an error (cross-platform `notify` quirks, missing inotify limit on Linux) would change the signature anyway. Principle 06 (complexity budget) speaks here: a `Result` wrapper around an infallible function adds noise without observable behaviour.

**Difference implies:**
The facade implies an error path that does not exist. A reader expecting fallible semantics writes `?` propagation that handles no real error.

**Disposition:**
**Facade moves — Wave 2 (facade-doc).** Narrow facade returns to `()`. If S70+ needs error propagation (a real `notify` failure surface emerges on some platform), both sides change together in a single commit. Add a footnote: "if watcher initialisation grows a real failure surface, both sides should change to `Result<(), CranelispError>` in lockstep — do not let them drift again." Prior disposition stands. Grounded in Principle 06 + the no-Decision-pins-fallibility observation.

### Finding F-7 — `pub fn current_module_name(&self) -> String` is announced only in passing

**Facade expects:**
Facade L131: `pub fn current_repl_module(&self) -> &ModuleFullPath;`. No companion String-returning accessor in the main `impl` block. The §"Coverage check" table at L1005 enumerates `current_module_name` as part of a long flat list of additional pub methods on `CompilerSession` (row classification: "extension/test-driven helpers").

**Source does:**
`pub fn current_module_name(&self) -> String` at `session_v4.rs:4059` — body: `self.current_module_path().to_string()`. Caller: `write_prompt` / `write_continuation_prompt` at `session_v4.rs:4066`.

**Design intent:**
The accessor is a one-line convenience for prompt display. No Decision pins its public status. Principle 02 (narrow interfaces) leans toward `pub(crate)` (the only caller is the prompt renderer, inside int); Principle 13 (auditable surface) requires it appear by name in the facade if it stays `pub`.

**Difference implies:**
A reader of the facade's main `impl CompilerSession` block does not see `current_module_name`; sees `current_repl_module() -> &ModuleFullPath` and infers they should call `.to_string()` on it. The actual source provides both. Per the baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline" — though int has no `public-api.txt`, the §"Coverage check" table IS the substitute), every pub item must be either named or marked internal-but-exposed with rationale; "named in passing within a long flat list" is the weakest possible form.

**Disposition:**
**Facade moves — Wave 2 (facade-doc clarification).** Promote `current_module_name` to a one-line entry under §"Coverage check" with the disposition "convenience accessor for prompt display; `pub` retained for symmetry with `write_prompt`" — OR narrow source to `pub(crate)` if no out-of-crate caller exists (tests at `session_v4.rs:5179+` do not appear to call it directly).

Default (facade-doc add) — lowest churn, no source change required. /design (int) Wave 2. Prior disposition stands; re-author grounds it in Principle 02 + 13 + baseline-diff discipline.

### Finding F-8 — `pub fn warnings_mut(&mut self) -> &mut Vec<Warning>` is unannounced

**Facade expects:**
Facade L146: `pub fn warnings(&self) -> &[Warning];` (immutable accessor). No mutable accessor named. §"Coverage check" at L1005 does not enumerate `warnings_mut`.

**Source does:**
`pub fn warnings_mut(&mut self) -> &mut Vec<Warning>` at `session_v4.rs:1680`, carrying `#[allow(dead_code)]` and the doc comment naming it the forward-deployed worker→session warning-merge entry-point. Currently no source caller. There is ALSO an `EvalResult::warnings_mut` method at `session_v4.rs:153` for a different type — two distinct `warnings_mut` accessors.

**Design intent:**
The accessor is forward-deployed for the worker→session warning-merge wiring that the facade L33 names as "S68 PIF residual" (per the §"Initiator-thread-only state" comment on `warnings: Vec<Warning>`). It exists in source so that when the merge wiring lands (PIF residual closure per FIXME 0109 worker decomposition), the merge code has a write entry-point already published. The grounding is Principle 13 (every public type / public method appears in the facade or is marked internal-but-exposed) + the S67 PIF discipline named on facade L33.

**Difference implies:**
A reader of the facade does not see the merge entry-point; sees only the read accessor and might assume warnings flow elsewhere. The forward-deployed-for-S68 intent is invisible in the facade.

**Disposition:**
**Facade moves — Wave 2 (facade-doc).** Add `warnings_mut` as a one-line accessor under the "REPL display + IO" or "Settings + paths" block, with a doc-comment "merge entry point for worker→session warning flow (S68 PIF residual per L33)." OR narrow source to `pub(crate)` (the merge wiring is internal to int per FIXME 0109 worker subsystem). Default: facade-doc add — once the merge wiring lands, an alternate REPL driver may want the accessor too; the forward-deployed-for-merge intent is the binding rationale.

/design (int) Wave 2. Prior disposition stands; re-author confirms grounded in Principle 13 + the S67-stated PIF discipline.

### Finding F-9 — `pub fn lookup_special_form(&self, name: &str) -> Option<String>` is unannounced + Principle-07 duplication

**Facade expects:**
The facade prescribes `describe_symbol(name) -> Option<SymbolDescription>` at L128 with a `SymbolCategory::SpecialForm` variant for the return. No separate `lookup_special_form` accessor.

**Source does:**
`pub fn lookup_special_form(&self, name: &str) -> Option<String>` at `session_v4.rs:3734`. Body: probes the root `""` module's `SymbolTable` for `ModuleEntry::Def` with `DefKind::SpecialForm { description }` and returns the description string. Used by `format_special_form_display` (`session_v4.rs:3725`) which is invoked from the sig handler.

`describe_symbol` at `session_v4.rs:1485-1538` goes through `current_symbol_table().get(name)` which falls back to root, and matches `DefKind::SpecialForm { .. }` to set the category — but does **not** reuse the `description` string from the kind (the SpecialForm branch sets `docstring = None`).

**Design intent:**
Principle 07 (single source of truth) — "When a concept (ISA flags, heap classification, primitive type names, structural decls, code pointers) appears in two places, it will diverge." The special-form-description lookup happens via TWO code paths today: `lookup_special_form` (probes the root module, returns the description string) and `describe_symbol`'s SpecialForm branch (probes the same root module via `current_symbol_table().get`, fails to populate `docstring`). The two paths both read from `ModuleEntry::Def { kind: DefKind::SpecialForm { description } }` — the canonical home is one. There IS duplication, and Principle 07 prescribes consolidation.

**Difference implies:**
A reader of the facade does not see the split; infers `describe_symbol` is the unified accessor. An alternative consumer outside int that calls `describe_symbol` to surface special-form documentation receives `docstring = None` — the bug. Meanwhile `lookup_special_form` is `pub` but used only by int's own slash-command formatter.

**Disposition:**
**Source moves — Wave 3 (Principle 07 cleanup).** `describe_symbol`'s SpecialForm branch should set `docstring = Some(description.clone())` by reading the kind, after which `lookup_special_form` either narrows to `pub(crate)` (the only caller is `format_special_form_display`) or deletes outright in favour of inline `describe_symbol(name).map(|d| d.docstring)`.

/dev (int) Wave 3. Prior disposition stands; **re-author flip vs prior framing:** the prior audit named this as "either narrow source to pub(crate) OR promote in facade" and treated them as equivalent options. Principle 07 grounds the binary: source moves, because the duplication itself is the architectural defect; promoting both to the facade enshrines the duplication. The prior audit's split-the-difference framing missed the principle.

### Finding F-10 — `SymbolDescription.related: Vec<FQSymbol>` populated as empty stub

**Facade expects:**
Facade L520-527: `pub struct SymbolDescription { fq, category, scheme, docstring, source, related: Vec<FQSymbol> }`. The `related` field is documented as "related symbols — defn, impl, match arms, etc." Per `repl/spec.md` §3.6 the universal-display format paths use related-symbol comment lines (`; defn:`, `; impl:`, `; match:`).

**Source does:**
`SymbolDescription` exists at `session_v4.rs:616-623` with the `related: Vec<FQSymbol>` field as facade-prescribed. The only construction site, `describe_symbol` at `session_v4.rs:1530-1537`, populates `related: Vec::new()` unconditionally. FIXME 0194 names this directly.

**Design intent:**
Facade L403 + `repl/spec.md` §3.6 + FIXME 0194 form the grounding chain. The field is target-stating; the population logic is what's missing. The REPL slash-command output (`/info name`) computes related-symbol comments through a separate path (the universal-display formatter at `format_def_entry`) and bypasses `describe_symbol`. So the facade's intent — `describe_symbol` as the unified accessor returning the full related-symbol list, with no caller duplicating cross-ref logic — is unmet. Principle 07 (single source of truth) is at stake again: the duplication between `describe_symbol`'s empty-related and `format_def_entry`'s computed-related is exactly the divergence Principle 07 forecloses.

**Difference implies:**
Any caller reading `description.related` always sees an empty vector. Test harnesses asserting cross-ref correctness, a future LSP server using `describe_symbol`, etc., get incorrect data while `/info` shows the right thing — the worst kind of divergence (the "fast path" works, the "slow path" silently lies).

**Disposition:**
**Source moves — Wave 3 (continued).** This is exactly FIXME 0194. The field is reachable, the writer is the right place, the population logic is what's missing. FIXME 0194's proposed resolution names the three collectors (defn-related, impl-related, match-related) and the wire-in point (`session_v4.rs:1530` in current source). Folds into /dev (int) Wave 3 work list. The facade text stays — it correctly names the target; the source closes the gap.

Prior disposition stands; re-author confirms grounded in FIXME 0194 + `repl/spec.md §3.6` + Principle 07.

### Finding F-11 — `module_imports` returns degraded synthetic `ImportSpec`s

**Facade expects:**
Facade L129: `module_imports(module) -> Vec<ImportSpec>`. The facade implies the parse-time `ImportSpec` is faithfully recoverable (alias, span, multi-name preserved).

**Source does:**
`pub fn module_imports(&self, module: &ModuleFullPath) -> Vec<cranelisp_types::ImportSpec>` at `session_v4.rs:1592`. The implementation note at L1583-1591 documents: "Per-binding reconstruction shape: `ModuleEntry::Import` stores only the source `FQSymbol` per binding; the parse-time `ImportSpec` is not retained on the symbol table. Each returned spec is therefore a single-name `Specific([local_name])` against the source module, with `alias = None` and `span = Span::SYNTHETIC`."

**Design intent:**
The facade target is faithful recovery. The grounding is `repl/spec.md` §3 (self-documenting REPL — `/imports` must show the original import as the user wrote it) + Principle 07 (the parse-time spec IS the single source of truth; reconstructing a degraded shape at read time creates a second authority). FIXME 0194's tail paragraph names the structural change required (sidecar store on `SymbolTable` per module per import; or per-binding retention of the originating `ImportSpec`).

**Difference implies:**
Shape is right (`Vec<ImportSpec>`); BEHAVIOUR is degraded — every spec is synthetic. Downstream consumers (LSP, test harness asserting "this module imports X as Y" with the alias intact, refactoring tools doing "rename across imports") receive `alias = None` always and `Span::SYNTHETIC`. The /imports slash-command display works because it does not depend on alias/span fidelity; richer consumers do not.

**Disposition:**
**Source moves — deferred to S70 (with rationale named).** The structural change required (sidecar store on `SymbolTable` per module per import) is a typed-store extension, not a one-call fix. Disposition by skill split:
- /design (int) Wave 2: add a doc-comment to facade L129 — "current implementation degrades to synthetic single-name `Specific` specs; alias/multi-name/span recovery tracked by FIXME 0194 tail." Makes the gap legible.
- /dev (int) S70+: close the gap structurally per FIXME 0194's tail proposal — extend `SymbolTable` with per-module/per-import sidecar, populate at import-registration time, drain at `module_imports` read time.

The structural decision (sidecar shape, retention strategy) is /arch's at S70 scope — recorded in arbitration A-3 below.

Prior disposition stands; re-author confirms grounded in FIXME 0194 + Principle 07.

### Finding F-12 — `set_lib_dirs / set_platform_dirs / push_platform_dir` ARE announced (no drift, recorded)

**Facade expects:**
Facade L143-144 has read accessors `lib_dirs() -> Vec<PathBuf>` and `platform_dirs() -> Vec<PathBuf>`. §"Coverage check" table at L1005 names `set_lib_dirs, set_platform_dirs, push_platform_dir` as "extension/test-driven helpers."

**Source does:**
`pub fn set_lib_dirs` at `session_v4.rs:1198`, `set_platform_dirs` at `1205`, `push_platform_dir` at `1212`. Test-driven runtime reconfiguration. Aligned with facade.

**Design intent:**
Announced in coverage table — facade discipline met. No grounding question.

**Disposition:**
**No drift.** Recorded so a future audit doesn't re-flag. Prior disposition stands.

### Finding F-13 — `poll_and_reload` IS announced (no drift, recorded)

**Facade expects:**
Not in main `impl CompilerSession` block. §"Coverage check" L1005 lists it.

**Source does:**
`pub fn poll_and_reload(&mut self) -> Vec<String>` at `session_v4.rs:1710`. Returns user-visible reload-result messages per `repl/spec.md §14`. Caller: `main.rs:278` (REPL loop iterator).

**Disposition:**
**No drift.** Recorded. Prior disposition stands.

### Finding F-14 — `re_register_module` Result wrapper around infallible call

**Facade expects:**
> `pub fn re_register_module(&mut self, module: &ModuleFullPath) -> Result<bool, CranelispError>;` (facade L43, comment notes "thin forward to `self.shared.scheduler.re_register_module(module)`").

**Source does:**
`pub fn re_register_module(&mut self, module: &ModuleFullPath) -> Result<bool, CranelispError>` at `session_v4.rs:2037-2042`. Body: `Ok(self.shared.scheduler.re_register_module(module))`. Per the doc comment: "The `Result` wrapper is reserved for future error propagation; the scheduler's `re_register_module` itself is infallible today."

**Design intent:**
Forward-deployed-fallibility — when re-registration grows a real failure mode (cache invalidation IO error, schema-version mismatch on reload, registered-module-failed re-entry), the Result wrapper absorbs it without a public-API break. Documented intent in source matches facade.

**Disposition:**
**No drift.** Recorded for completeness. Prior disposition stands.

### Finding F-15 — Exe-bundle force-link re-exports not enumerated in facade (FIXME 0214)

**Facade expects:**
Facade has §"Exe-bundle startup contract — `cranelisp_init_primitives()`" (referenced from L34 of `crates/cranelisp-exe-bundle/src/lib.rs`). The section describes the startup-hook discipline generally and points to `facades/intrinsics.md`. **No enumeration of the 8 retained intrinsics submodule re-exports.**

**Source does:**
`crates/cranelisp-exe-bundle/src/lib.rs` lines 37-49 contains 8 `pub use cranelisp_intrinsics::*` lines:
1. `pub use cranelisp_intrinsics::alloc;` (L38) — heap allocator surface
2. `pub use cranelisp_intrinsics::drop;` (L39) — drop-glue trampolines
3. `pub use cranelisp_intrinsics::io;` (L40) — IO trampoline + token machinery
4. `pub use cranelisp_intrinsics::ivar;` (L41) — IVar runtime
5. `pub use cranelisp_intrinsics::panic;` (L42) — panic handler
6. `pub use cranelisp_intrinsics::rc;` (L43) — reference counting primitives
7. `pub use cranelisp_intrinsics::heap_string as intrinsics_string;` (L48) — heap-string allocator/reader
8. `pub use cranelisp_intrinsics::vec_runtime as intrinsics_vec;` (L49) — vec runtime

The 8 lines appear in `crates/cranelisp-exe-bundle/public-api.txt` L2-9 as the first 8 entries. Purpose per the lib.rs crate-level docs at L12-23: DCE-prevention — `cargo`'s linker would discard the unreferenced extern fns from `cranelisp-intrinsics` without them. A separate `pub use cranelisp_intrinsics::trace` line was DELETED per Decision 40 Path B1 (S67 W4) — `--link` mode rejects `(trace ...)` at compile time, so the staticlib does not need trace symbols.

**Design intent:**
The grounding chain is precise: `design/arch/CLAUDE.md §"Baseline-diff discipline"` — "every pub-api line in the baseline is named in the corresponding facade (or marked internal-but-exposed with rationale)" — + Decision 0043 (runtime split into primitives + intrinsics; the 8 re-exports are intrinsics submodules that the staticlib must retain) + Decision 0048 §"Structural invariant — backend dep-ban" (the entire exe-bundle force-link discipline exists because backend cannot directly reference primitives; the staticlib must pull intrinsics in via these re-exports so that JIT-emitted-call targets resolve at staticlib link time) + Principle 18 (enforce structurally) — the re-exports ARE the structural enforcement that the symbols land in the `.a`; lose them and the linker strips them.

The 8 re-exports are NOT optional or transient — they are load-bearing for the staticlib's contents. Principle 07 (single source of truth): if the facade is the as-designed contract, the 8 re-exports' purpose belongs there.

**Difference implies:**
The facade-compliance test scaffolded in S67 W0 would fail this check. Eight `public-api.txt` lines unnamed in the facade is exactly the kind of drift the baseline-diff discipline is designed to catch — and it is caught, by FIXME 0214 itself, which is the open work register's claim on this gap.

**Disposition:**
**Facade moves — Wave 2 (closes FIXME 0214).** Add an enumerated bullet list in `facades/int.md` §"Exe-bundle startup contract" (after the description of `cranelisp_init_primitives`) naming each re-export with its purpose:

```
Force-link re-exports retained from `cranelisp-intrinsics` (DCE-prevention; without these, the linker strips unreferenced `#[no_mangle]` fns from the staticlib):

- `alloc` — heap allocator surface (`cranelisp_intrinsics::alloc`)
- `drop` — drop-glue trampolines (`cranelisp_intrinsics::drop`)
- `io` — IO trampoline + token machinery (`cranelisp_intrinsics::io`)
- `ivar` — IVar runtime (`cranelisp_intrinsics::ivar`)
- `panic` — panic handler (`cranelisp_intrinsics::panic`)
- `rc` — reference counting primitives (`cranelisp_intrinsics::rc`)
- `intrinsics_string` — heap-string allocator/reader (alias of `cranelisp_intrinsics::heap_string`)
- `intrinsics_vec` — vec runtime (alias of `cranelisp_intrinsics::vec_runtime`)

`trace` was DELETED per Decision 40 Path B1 (S67 W4): `--link` rejects `(trace ...)` at compile time via the architecture's natural missing-symbol detection.
```

Also adopt the two stylistic suggestions from FIXME 0214:
- Facade pseudocode at L965 — align `Arc::clone(&*PRIMITIVES_TABLE)` with implementation `(*PRIMITIVES_TABLE).as_ref().clone()` (semantically equivalent; align the prose).
- Cite Principle 18 by number where Decision 0048's explicit init-hook discipline is the motivating example.

/design (int) Wave 2 — single commit closes FIXME 0214. Prior disposition stands; re-author confirms grounded in baseline-diff discipline + Decisions 0043 + 0048 + Principle 18.

### Finding F-16 — Facade-prescribed per-FQ scheduler waits (`wait_for_inmem(fq)`, `wait_for_typecheck_symbol(fq)`, `wait_for_typecheck_type(fqt)`, `priority_boost_jit(fq)`, plus `wait_for_typecheck(module)` for module-granularity) do not exist in source

**Facade expects:**
Facade L607-612 enumerates the per-symbol coordination surface:
```
pub fn wait_for_typecheck(&self, module: &ModuleFullPath) -> Result<(), SchedulerError>;       // block until module typecheck-done
pub fn wait_for_typecheck_symbol(&self, fq: &FQSymbol) -> Result<(), SchedulerError>;          // FQ form retry path
pub fn wait_for_typecheck_type(&self, fqt: &FQTypeName) -> Result<(), SchedulerError>;         // FQTypename retry path
pub fn wait_for_inmem(&self, fq: &FQSymbol) -> Result<(), SchedulerError>;                     // expansion needs jitted macro
pub fn priority_boost_jit(&self, fq: &FQSymbol);                                               // promote symbol's JIT to head of queue
pub fn block_for_macro_codegen(&self, fq: &FQSymbol) -> Result<(), SchedulerError>;            // eval per-closure-dep wait
```

The facade's `process_cluster::handle_gap` pseudocode (L1113-1141) drives them per gap variant:
- `ResolutionGap::SymbolTypechecked(fq)` → `ensure_registered + wait_for_typecheck_symbol(fq)`.
- `ResolutionGap::MacroInMem(fq)` → `ensure_registered + wait_for_typecheck_symbol(fq) + peek-kind + (priority_boost_jit(fq) + wait_for_inmem(fq) if macro-needs-code)`.
- `ResolutionGap::Type(fqt)` → `ensure_registered + wait_for_typecheck_type(fqt)`.

**Source does:**
`src/scheduler.rs` has these wait methods (grep confirmed):
- `wait_inmem_complete()` at L930 — whole-session non-blocking check.
- `wait_inmem_complete_blocking()` at L992 — whole-session blocking wait.
- `wait_module_inmem_complete_blocking(target: &ModuleFullPath)` at L959 — per-MODULE blocking wait.
- `wait_object_complete()` at L1021.
- `block_for_macro_codegen(fq)` at L669 — per-symbol macro-codegen wait (exists, facade-named).

**Absent from source**: `wait_for_inmem(fq)`, `wait_for_typecheck(module)`, `wait_for_typecheck_symbol(fq)`, `wait_for_typecheck_type(fqt)`, `priority_boost_jit(fq)`. Five facade-prescribed methods do not exist as named methods. The actual coordination granularity is per-module (`ModulePool` state machine + `ModuleSuspendState`), not per-FQSymbol — with the single exception `block_for_macro_codegen` which IS per-FQ.

`src/cluster.rs` confirms: no `handle_gap` function exists. `process_cluster` at `cluster.rs:177` is the Wave 3a-β scaffold that delegates to `worker::check_program_compat` against `ClusterContext::Live`, returns `ProcessedCluster::empty()`. The gap-retry envelope is documented as the **target shape** in the function's doc comment ("**Target shape** (per `design/arch/facades/int.md` §"process_cluster")...") with the note "**Current state** (Wave 3a-β in-flight): ... the staging-vs-live pivot to `ClusterContext::Cluster` is FIXME 0176's responsibility."

**Design intent:**
This is the single most consequential finding in the audit. The grounding chain is **deep and explicit**:

1. **Decision 0044** (Cluster-atomic typecheck via orchestrator-owned staging; 2026-05-13 third amendment) — the canonical `check_forms(parsed, &mut ctx, symbol_tables) -> Result<(), CheckError>` surface. The `CheckError::Gap(ResolutionGap)` variant is the binding return type for any typecheck-driven gap. The orchestrator's role is to "catch each gap, dispatch via handle_gap → ensure_registered + wait + (priority_boost + wait_for_inmem)" — per the facade's own §"process_cluster — the cluster-atomic orchestration loop" §"Atomicity guarantees".
2. **`sequences/exec-flow-compilation.mmd` lines 77, 81, 86, 87, 125, 129, 136, 140** — explicit sequence-diagram steps showing `process_cluster` → `Scheduler::wait_for_typecheck_symbol(fq)` / `Scheduler::priority_boost_jit(fq)` / `Scheduler::wait_for_inmem(fq)` / `Scheduler::wait_for_typecheck_type(fqt)`. These are the binding sequence-diagram steps for the post-Decision-44 worker dispatch path. The `†` marker convention in `exec-flow-repl.mmd` L9 marks proposed/target API; the L80 / L112 lines in that file carry `†` for `wait_for_inmem_codegen` and `wait_for_inmem(fq)`.
3. **`src/CLAUDE.md` §"Cluster-Atomic Orchestration (Sprint 66 Wave 3a-β)"** — explicitly names the status: "`process_cluster` is the SOLE crate-crossing where `ResolutionGap` values become scheduler calls. ... Status (Sprint 66 Wave 3b-2c.2): `process_cluster` delegates to `worker::check_program_compat`. The staging-commit/discard infrastructure (`worker::process_cluster_with_staging` + `worker::commit_staging_to_live`) is wired and tested by inspection but **not yet activated on the hot path** — `check_program_compat` continues to use `ClusterContext::Live` pending FIXME 0179 (cluster-mode read-union of staging and live)."
4. **FIXME 0179** (open) — names the cluster-mode read-union as the blocker for `ClusterContext::Cluster` activation on the hot path. Until it lands, `process_cluster` cannot drive gap-retry meaningfully because there is no Cluster-mode `check_forms` execution to produce per-FQ gaps.
5. **FIXME 0176** — owns the staging pivot. The per-FQ waits cannot land until the gap-retry envelope can be exercised, which depends on Cluster mode being active.

**This is target-stating, not stale-facade.** Decision 0044 is pre-implementation. The sequence diagrams are the canonical target. The facade L607-612 enumeration of per-FQ waits is the binding shape for the post-cluster-atomic scheduler surface. The current source `wait_module_inmem_complete_blocking` is the as-built per-module variant — useful as a transitional shape, but NOT the destination.

**Difference implies:**
The prior audit treated this as "the facade should mark each as target-shape; source rev3 diagnostic" — splitting "both move" between Wave 2 facade-doc and Wave 3 source diagnostic. The grounding shows this framing is incomplete:

- The facade is **already** target-stating; the L607-612 enumeration IS the announced-target shape, exactly as Decision 0044 + the sequence diagrams require. **The facade does not "move" here — it already says the right thing.** What the facade could add is an explicit "(target — pending FIXME 0176/0179)" annotation on these rows, consistent with how other rows mark deferred work (e.g., L43 on `re_register_module`, L115-126 on the introspection-accessor family).
- The source **must** move to land these methods. The grounding is Decision 0044 (binding) + sequence diagrams (binding) + FIXMEs 0176 + 0179 (open work register tracking the gap). "Source moves" is the binary disposition.

**Disposition:**
**Source moves — Wave 3 (Cluster-mode activation) + Facade adds deferral marker — Wave 2.**

For Wave 2 (facade): on facade L607-612 rows for `wait_for_typecheck`, `wait_for_typecheck_symbol`, `wait_for_typecheck_type`, `wait_for_inmem`, `priority_boost_jit`, add a one-line annotation: "(target — source lands when FIXME 0176 activates `ClusterContext::Cluster` on the hot path; depends on FIXME 0179 cluster-mode read-union landing first)." This makes the deferral legible without changing the binding target shape. The facade comment on `re_register_module` (L43) is the precedent — "Sprint 67 W1 PIF target — thin forward to `self.shared.scheduler.re_register_module(module)` (currently only `CompileScheduler::re_register_module` exists at `scheduler.rs:412`; the `CompilerSession`-level forward lands in W3)."

For Wave 3 (source): the implementation order per the grounding is:
1. FIXME 0179 — cluster-mode read-union of staging and live in `TypeCheckEnv::current_symbol_table`. Owner: /typecheck (filed targeting /design but resolves with typecheck-side surgery per Decision 0044 + Principle 17 module-locality).
2. FIXME 0176 — `ClusterContext::Cluster` activation on the hot path in `process_cluster`. Owner: /dev (int). Requires 0179.
3. The five per-FQ scheduler methods: `wait_for_typecheck(module)`, `wait_for_typecheck_symbol(fq)`, `wait_for_typecheck_type(fqt)`, `wait_for_inmem(fq)`, `priority_boost_jit(fq)`. Owner: /dev (int) on `CompileScheduler`. Requires 0176.
4. `handle_gap` function in `src/cluster.rs` per the facade L1113-1141 pseudocode. Owner: /dev (int). Requires the five methods.

This is a multi-sprint sequence (S69 W3 may complete 0179 + 0176; the per-FQ methods + handle_gap may stretch into S70). The facade-deferral marker (Wave 2) is what gives the deferral structural visibility.

**Re-author flip vs prior framing:** The prior audit's framing — "Both move" — was right in shape (facade adds annotation, source moves) but wrong in proportion and grounding. The prior text framed the facade-side change as "make the gap legible" without naming the Decision-44-bound target-stating intent; it implied the facade was over-prescribing per-FQ waits when the per-module shape was "the settled architecture." The grounding shows the opposite: per-FQ is the settled architecture (Decision 0044 + sequence diagrams), per-module is the as-built transitional shape. The flip is in **which side carries the binding intent**: the facade does, not the source.

The prior audit also implicitly assumed `wait_for_inmem(fq)` exists when constructing F-17's rev3 hypothesis. The re-author makes that explicit (see F-17).

### Finding F-17 — rev3 root-cause investigation re-rooted with grounding

**Context:**
The prior audit's F-17 attempted to re-root the rev3 hypothesis ("30s timeout on `/info add-i64`") against three new candidates (Hypothesis A startup blocking, B macro-codegen wait, C leaked workers). The re-author confirms the **structural correction** (no per-FQ wait exists, so the original hypothesis is impossible) and adds Decision-grounded analysis to each candidate.

**Design intent — grounding the three hypotheses:**

1. **Hypothesis A (startup-time prelude registration timing).** Grounding: Decision 0030 (form-by-form scheduler deadlocks on mutual imports — environmental constraint future readers will hit) + Decision 0031 (one JITModule per compile batch; reclaim semantics). If a prelude module gets registered and its typecheck cannot complete (because of cycle, gap, or a worker leak), `wait_inmem_complete_blocking` parks until the work completes — which is the binding correctness shape per Decision 0030. The 30s manifests at REPL startup *because the REPL has no prompt yet* — main.rs:205 calls `s.wait_inmem_complete()` (non-blocking variant) but `s.register_module(entry_module_name)?` at `main.rs:172` (which calls `register_entry_module` → `register_module_with_source` → `wait_inmem_complete_blocking` at `session_v4.rs:2085`) IS the blocking call. If this is the actual hang, the symptom "30s on /info" is mis-attributed to /info; it is actually 30s at startup, /info just happens to be the user's first input that fires after the prompt finally appears.

2. **Hypothesis B (`block_for_macro_codegen` interaction with `Code::Primitive`).** Grounding: Decision 0048 §"Structural invariant — backend dep-ban" — primitives are dispatched through GOT, never via direct call. `Code::Primitive` is the marker variant (no payload) per Decision 0048 A2 amendment. `Code::Primitive::ptr()` returns `std::ptr::null()` per `crates/cranelisp-backend/src/code.rs:151`. **If** `block_for_macro_codegen(fq)` is called against a primitive FQ, and the implementation waits for a `Code::Jit` finalisation event that never fires (because primitives never go through JIT — they are statically initialised at LazyLock), the wait parks forever. The architectural defence is `block_for_macro_codegen` short-circuiting when the target entry's `Code` is `Code::Primitive` — which is a one-line guard against an invariant violation. **However**, `/info name` does NOT expand macros (it is slash-command parse-and-dispatch, not form eval), so this hypothesis is structurally unlikely unless there is a hidden macro expansion in the slash-command flow.

3. **Hypothesis C (worker leak across test runs).** Grounding: `CompilerSession::Drop` is documented at `session_v4.rs:3888` as a safety net for `shutdown()`. If the test fixture's session goes out of scope without `shutdown()` being called explicitly, the worker pool's `JoinHandle`s may leak — workers still draining a previous test's work queue could block on `register_module` for a module the new test hasn't published sexps for. The narrow test passes because the fixture-construction order is correct; the broader suite test fails because of leaked worker threads from a prior test's failure path. The architectural defence: `CompilerSession::Drop` must enforce `shutdown()` — which is a Principle 18 (enforce structurally) opportunity.

**Difference implies — what is actually known:**
The prior audit's named fix sites in the rev3 brief (`src/cluster.rs::handle_gap` and `src/session_v4.rs::describe_symbol`) are **both wrong** under the re-author's grounding:
- `cluster.rs` has no `handle_gap` function today (F-16 confirms; the facade pseudocode is the target shape). `process_cluster` at `cluster.rs:177` delegates to `worker::check_program_compat` and returns `ProcessedCluster::empty()` — no scheduler call could hang on `Code::Primitive` because no scheduler call is on the path at all.
- `describe_symbol` at `session_v4.rs:1485-1538` performs only non-blocking reads (`current_symbol_table().get(name)` + `resolve_entry_for_display` + `format_def_entry` + `get_introspection(name)`). There is no `wait_for_inmem(fq)` to short-circuit; there is no scheduler call at all.

**Disposition:**
**Source moves — Wave 3 investigation (not a single-line fix).** /dev (int) Wave 3 brief drives:

1. **Reproduce in isolation.** /qa folds `tests/repl_info_primitives.rs` (or similar) with a 3-line REPL-input test (`(defn id [x] x)\n/info add-i64\n`) — committed even if currently passing, per `memory/feedback_repros_join_suite.md` (repros join the suite for eternity). Confirms whether the hang is at startup (Hypothesis A) or at slash-command time (Hypothesis B / C).
2. **Enable scheduler trace.** Run with `CRANELISP_SCHEDULER_TRACE=1` (the `src/observability.rs` consumer per facade §"Observability"). Read the trace — is `wait_inmem_complete_blocking` parked on the completion condvar for 30s? On what module?
3. **Check primitives registration.** Verify `cranelisp_primitives::PRIMITIVES_TABLE` is referenced at session-init per Decision 0048, but the `primitives` module is NOT registered with the scheduler. If it is, the scheduler will wait forever for an `inmem_done` that never arrives — a Decision 0048 invariant violation. Principle 18: this should be enforced structurally (the registration call should refuse synthetic modules).
4. **Decide on the fix site after diagnosis.**
   - If A: fix in `register_module_with_source` or `wait_inmem_complete_blocking` — add a 30s ceiling with a meaningful error AND investigate which module never reaches `inmem_done` (likely a Decision 0030 cycle case).
   - If B: fix in `scheduler.rs::block_for_macro_codegen` to short-circuit when the target FQ's `Code` is `Code::Primitive` — restoring the Decision 0048 invariant.
   - If C: fix in `CompilerSession::Drop` to enforce `shutdown()` structurally (Principle 18).

**Defensive landing regardless of diagnosis: the failing repro becomes a committed test.** Per `memory/feedback_repros_join_suite.md`. /qa folds `tests/repl_info_primitives.rs` even if it currently passes — the diagnostic discipline is the durable record.

The prior audit's three-hypothesis structure stands; **re-author flip:** explicit Decision-grounding on each hypothesis names the architectural invariant at stake, which informs which fix site is structurally correct (vs. a band-aid). The prior audit treated the three fix sites as roughly equivalent options with pros/cons; the re-author shows each maps to a different Decision/Principle, and the right fix site depends on which architectural invariant is being violated.

### Finding F-18 — Coverage hole: `Code::Primitive` null-pointer discipline at `Code::ptr()` consumers

**Facade expects:**
Facade L957-975 §"Session init — referencing the static `PRIMITIVES_TABLE` (Decision 48)" describes the `Code::Primitive` marker variant. No facade text enumerates the null-pointer discipline at the call sites that consume `Code::ptr()`.

**Source does:**
`Code::Primitive::ptr()` returns `std::ptr::null()` per `crates/cranelisp-backend/src/code.rs:151`. Every site in int that does `c.ptr() as i64` and treats the result as a callable address relies on a separate null-filter check. The prior audit noted one such site (`session_v4.rs:2773 if code_ptr == 0 { continue; }`).

**Design intent:**
Decision 0035 §"post-rollback canonical statement" — "GOT is the single source of truth for callable addresses; `ptr` lives in `SymbolTable.got()` indexed by `ModuleEntry::Def.got_slot`. No per-entry pointer field." Decision 0048 A2 — "the `Code::Primitive` marker variant carries NO payload; it expresses lifecycle category (process-static, externally owned by this LazyLock) without naming an owned resource." Together: `Code::Primitive::ptr()` returning null is the **type-system encoding** of "Code does not own the callable address; GOT does." Principle 18 — enforce structurally: the null-discipline is the structural mechanism; the alternative (`unreachable!()` in `ptr()`) would also be valid per Principle 18 but breaks the uniform `c.ptr() as i64` pattern at consumers.

**Difference implies:**
A new code path that omits the null-check would crash. No mechanical test guards this. The facade does not name the discipline: "any `Code::ptr()` consumer in int must null-check, route through the GOT slot (Decision 0035 canonical path), or `unreachable!` for `Code::Primitive`."

**Disposition:**
**Facade moves — Wave 2 + Source moves — Wave 3 (audit).**

Wave 2 (facade): add a one-paragraph §"Code::Primitive null-pointer discipline" subsection to facade §"Session init — referencing the static `PRIMITIVES_TABLE`", naming the three-way discipline (null-check / route through GOT / unreachable) and citing Decisions 0035 + 0048 + Principle 18.

Wave 3 (source): audit every `Code::ptr()` consumer in `src/` to confirm each follows one of the three. This is the canonical Decision 0035 path made explicit: callable addresses live in the GOT, not in `Code`; `Code::Primitive::ptr()` returning null is the source-side type-system encoding of that invariant.

Arbitration A-4 below records the open question of `null` vs `unreachable!` (a /backend authority call).

Prior disposition stands; re-author confirms grounded in Decisions 0035 + 0048 + Principle 18.

### Finding F-19 — Coverage hole: slash-command set drift (no mechanical pin)

**Facade expects:**
Facade L496-502 names `SlashCommand` variants (per F-3, target-stating; current actual is private). §"Coverage check" does not enumerate the parsed slash commands.

**Source does:**
Per `session_v4.rs:285-308` (`parse_slash_command`), 22 commands: `/help`, `/quit`, `/sig`, `/doc`, `/type`, `/info`, `/list`, `/mem`, `/time`, `/expand`, `/imports`, `/exports`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/mod`, `/run-tests`, `/run-all-tests`, `/reset`, `/sh`. Each line is a string-literal match against the input.

**Design intent:**
`repl/spec.md` (REPL experience specification) is the binding source of truth for which slash commands exist and what they do — owned by `/repl`. The facade does not duplicate the slash-command enumeration; the binding source is the spec. Principle 13 (auditable surface) — the mechanical pin for the slash-command set is `/qa`'s E2E test suite that exercises each command per `repl/spec.md`. /design's facade does not own the pin.

**Difference implies:**
The slash-command parse set has no mechanical pin at the facade layer. Adding/removing a command is invisible to mechanical baseline-diff at the facade. The behavioural pin lives in /qa's E2E test suite, per `repl/spec.md` traceability annotations.

**Disposition:**
**Coverage hole; FYI.** No mechanical pin to add in `/design`'s scope. /qa's E2E suite owns the behavioural pin per `repl/spec.md` traceability. /design (int) Wave 2 adds a one-line note in §"Coverage check" pointing at /qa's test suite as the canonical pin location, citing `repl/spec.md` as the binding source.

Prior disposition stands; re-author confirms grounded in `repl/spec.md` ownership + Principle 13.

### Finding F-20 — Coverage hole: exe-bundle public-api ↔ facade alignment (resolved by F-15)

**Facade expects:**
The S67 W0 baseline-diff discipline says "every pub-api line in the baseline is named in the corresponding facade."

**Source does:**
`crates/cranelisp-exe-bundle/public-api.txt` is 11 lines. 8 are the intrinsics submodule re-exports (F-15). 2 are `cranelisp_init_primitives` + `cranelisp_init_platform` (named in facade per Decision 48 cascade + the lib.rs body). 1 is `pub mod cranelisp_exe_bundle` (the crate-level module declaration).

**Design intent:**
Per the baseline-diff discipline. F-15 closes the 8-line gap; the remaining 3 lines are already named.

**Disposition:**
**Coverage hole; resolved by F-15 in Wave 2.** Already on the work list. Prior disposition stands.

### Finding F-21 — `pub const QUIT_SENTINEL: &str = "\x00QUIT"` documented as internal-but-exposed

**Facade expects:**
Facade L954: `pub const QUIT_SENTINEL: &str = "\x00QUIT";` with note "session_v4.rs:215 — sentinel returned by `process_commands` on /quit; consumed by main.rs REPL loop. Internal-but-exposed: the binary entry point reads it."

**Source does:**
`pub const QUIT_SENTINEL: &str = "\x00QUIT";` at `session_v4.rs:215`. Aligned.

**Design intent:**
Internal-but-exposed marker is the right facade discipline per the baseline-diff convention — items that are `pub` for cross-module access within int but not for external consumption.

**Disposition:**
**No drift.** Recorded for completeness. The facade comment correctly flags it as internal-but-exposed. The doc-comment "Wave 3 may relocate to `pub(crate)` if no out-of-crate caller exists" is a S70+ consideration; not S69 scope. Prior disposition stands.

---

## Findings overview — with grounding citation

| # | Class | Disposition | Grounding | Owner | Sprint |
|---|---|---|---|---|---|
| F-1 | Hidden surface | Facade moves (remove `format_command_result`) | No Decision pins it; per-handler shape is settled | /design (int) | S69 W2 |
| F-2 | Hidden surface | Source moves (author `&self` method consulting introspection) | Decisions 0038 + 0041 + Principle 07 + `repl/spec.md §3` | /dev (int) | S69 W3 |
| F-3 | Shape drift + hidden | Facade moves (demote `SlashCommand` to documentary; drop `Reload`; add source extras) | Principles 02 + 13; no Decision pins public status | /design (int) | S69 W2 |
| F-4 | Shape drift | Source moves (narrow `register_module` arg to `&ModuleFullPath`) | `CLAUDE.md §"String Newtypes"` hard rule + Principle 18 | /dev (int) | S69 W3 |
| F-5 | Shape drift | Source moves (add `module` param + Result wrapper to `regenerate_backing_file`) | `repl/spec.md §15` + Principles 06 + 12 | /dev (int) | S69 W3 |
| F-6 | Shape drift | Facade moves (narrow `init_watcher` / `sync_watcher` returns to `()`) | No Decision pins fallibility; Principle 06 | /design (int) | S69 W2 |
| F-7 | Unannounced surface | Facade moves (clarify `current_module_name` in coverage table) | Principles 02 + 13 + baseline-diff discipline | /design (int) | S69 W2 |
| F-8 | Unannounced surface | Facade moves (add `warnings_mut` to coverage with merge-entry-point note) | Principle 13 + facade L33 PIF-residual statement | /design (int) | S69 W2 |
| F-9 | Unannounced surface + Principle-07 duplication | Source moves (close `describe_symbol`'s SpecialForm gap; then narrow `lookup_special_form` to `pub(crate)`) | Principle 07 + `repl/spec.md §3` | /dev (int) | S69 W3 |
| F-10 | Coverage hole | Source moves (populate `SymbolDescription.related` per FIXME 0194) | FIXME 0194 + `repl/spec.md §3.6` + Principle 07 | /dev (int) | S69 W3 |
| F-11 | Shape drift (partial) | Facade-doc partial (S69 W2); source S70+ for full ImportSpec recovery | FIXME 0194 tail + `repl/spec.md §3` + Principle 07 | /design (int) + /dev (int) | S69 W2 / S70+ |
| F-12 | (recorded) | No drift | Announced in coverage table | — | — |
| F-13 | (recorded) | No drift | Announced in coverage table | — | — |
| F-14 | (recorded) | No drift | Forward-deployed-fallibility documented in source | — | — |
| F-15 | Unannounced surface | Facade moves (enumerate 8 exe-bundle re-exports; close FIXME 0214) | Baseline-diff discipline + Decisions 0043 + 0048 + Principle 18 | /design (int) | S69 W2 |
| F-16 | Hidden surface (scheduler — load-bearing) | Source moves (per-FQ waits + handle_gap land in Wave 3+); facade adds deferral marker (Wave 2) | **Decision 0044 + `sequences/exec-flow-compilation.mmd` + `src/CLAUDE.md` §"Cluster-Atomic Orchestration" + FIXMEs 0176 + 0179** | /design (int) + /dev (int) | S69 W2 / S69 W3+ |
| F-17 | rev3 root-cause | Source moves (Wave 3 investigation + tests/ repro per fail-suite discipline) | Decisions 0030 + 0031 + 0048 + Principle 18 | /dev (int) + /qa | S69 W3 |
| F-18 | Coverage hole | Facade moves + Source moves (document `Code::Primitive` null-pointer discipline + audit consumers) | Decisions 0035 + 0048 + Principle 18 | /design (int) + /dev (int) | S69 W2 + S69 W3 |
| F-19 | Coverage hole | (FYI — /qa E2E owns the pin) | `repl/spec.md` + Principle 13 | — | — |
| F-20 | Coverage hole | Resolved by F-15 | Baseline-diff discipline | — | — |
| F-21 | (recorded) | No drift | Internal-but-exposed convention | — | — |

**Class totals:**
- Hidden surface (facade items absent from source): 4 (F-1, F-2, F-3 partial, F-16).
- Unannounced surface (source items absent from facade): 4 (F-7, F-8, F-9, F-15).
- Shape drift (items in both, described differently): 5 (F-3, F-4, F-5, F-6, F-11).
- Coverage holes (no mechanical pin): 5 (F-10, F-18, F-19, F-20, plus F-17 as rev3 diagnostic-not-fixable-by-pin).

---

## Calibration of prior dispositions — re-author flips and confirmations

Per `memory/feedback_audit_per_item_analysis.md`: "every 'facade moves' disposition must be re-examined: was the facade target-stating (source owes migration) or genuinely stale (facade moves correctly)? The re-classification needs the architectural configuration loaded; it cannot be done from the audit text alone."

| # | Prior disposition | Re-author disposition | Flip? | Substantive change |
|---|---|---|---|---|
| F-1 | Facade moves | Facade moves | No | Confirmed; added grounding (no Decision pins centralisation) |
| F-2 | Source moves | Source moves | No | Confirmed; added Decision 0038 + 0041 + Principle 07 + spec §3 grounding |
| F-3 | Facade moves (demote) + Source acknowledged | Facade moves (demote) | No | Confirmed; flipped framing from YAGNI to Principles 02 + 13 grounding |
| F-4 | Source moves | Source moves | No | Confirmed; flipped framing from "trivial narrowing" to "hard-rule grounding" (CLAUDE.md §"String Newtypes" + Principle 18) |
| F-5 | Source moves (partial) | Source moves (partial) | No | Confirmed; added `repl/spec.md §15` + Principles 06 + 12 grounding |
| F-6 | Facade moves | Facade moves | No | Confirmed; added Principle 06 + no-Decision-pins-fallibility grounding |
| F-7 | Facade moves (clarify) | Facade moves (clarify) | No | Confirmed; added baseline-diff-discipline grounding |
| F-8 | Facade moves (add) | Facade moves (add) | No | Confirmed; added facade-L33-PIF-residual grounding |
| F-9 | Source moves OR facade moves (split) | **Source moves (binary)** | **YES** | **Principle 07 grounds the binary** — duplication itself is the defect; promoting both to the facade enshrines it. Prior split-the-difference framing missed the principle. |
| F-10 | Source moves | Source moves | No | Confirmed; added Principle 07 + spec §3.6 grounding |
| F-11 | Source moves (deferred) | Source moves (deferred) | No | Confirmed; added Principle 07 + spec §3 grounding |
| F-12 | No drift | No drift | No | — |
| F-13 | No drift | No drift | No | — |
| F-14 | No drift | No drift | No | — |
| F-15 | Facade moves | Facade moves | No | Confirmed; added Decisions 0043 + 0048 + Principle 18 grounding |
| F-16 | **Both move** (facade adds annotation, source diagnostic) | **Source moves (binding); facade adds deferral marker (subordinate)** | **YES** | **Decision 0044 + sequence diagrams ground per-FQ waits as the SETTLED architecture, not the as-built per-module variant. Facade does not "move" — it already says the right thing. Prior framing implied facade was over-prescribing; grounding shows it under-marks deferral on rows that ARE target-stating-correctly.** |
| F-17 | Source moves (Wave 3 investigation) — three fix-site candidates equivalent | **Source moves (Wave 3 investigation) — three fix-site candidates each map to a different Decision/Principle invariant** | **YES (framing)** | **Each hypothesis maps to a different architectural invariant** (A → Decision 0030 cycles; B → Decision 0048 GOT-dispatch invariant; C → Principle 18 enforce-structurally on Drop). The correct fix site depends on which invariant is being violated, not on pros/cons of the three candidates as equivalent options. |
| F-18 | Facade moves + Source moves | Facade moves + Source moves | No | Confirmed; added Decisions 0035 + 0048 + Principle 18 grounding |
| F-19 | Coverage hole; FYI | Coverage hole; FYI | No | Confirmed; added `repl/spec.md` ownership + Principle 13 grounding |
| F-20 | Resolved by F-15 | Resolved by F-15 | No | Confirmed |
| F-21 | No drift | No drift | No | — |

**Flip count: 3 substantive flips (F-9, F-16, F-17), of which two (F-16 + F-17) re-root the rev3 framing on Decision 0044 + sequence-diagram grounding.** The remaining 18 dispositions are confirmed in shape; 14 of those gain explicit Decision/Principle/FIXME grounding citations that the prior audit lacked.

**The most consequential flips are F-9, F-16, and F-17:**
- **F-9** — the prior audit's "source moves OR facade moves" framing missed that Principle 07 makes the disposition non-binary: the duplication is the defect; consolidation is the fix; promoting both to the facade would enshrine the duplication.
- **F-16** — the prior audit framed the 5 per-FQ scheduler waits' absence-from-source as "facade may be over-prescribed; mark target-shape." The grounding (Decision 0044 + sequence diagrams `exec-flow-compilation.mmd` + `src/CLAUDE.md §"Cluster-Atomic Orchestration"` + FIXMEs 0176 + 0179) shows the opposite: per-FQ is the settled architecture; per-module is the as-built transitional. The facade is already correct; source must land the methods. The disposition is "source moves" with a facade-side deferral annotation as subordinate task, not "both move" with equal weight.
- **F-17** — the prior audit named three fix sites for the rev3 hang as roughly equivalent options. Grounding shows each maps to a different architectural invariant (Decision 0030 cycles; Decision 0048 GOT-dispatch; Principle 18 Drop-discipline), and the correct fix depends on which invariant is being violated — not on pros/cons.

---

## Arbitration briefs — what the audit cannot resolve alone

### A-1 — rev3 fix site (depends on reproduction; cross-Decision)

**Question.** The 30s timeout on `/info add-i64` cannot be re-rooted in `wait_for_inmem(fq)` (which does not exist in source per F-16). Three hypotheses (A startup blocking, B macro-codegen wait, C leaked workers) each map to a different Decision/Principle (per F-17). The audit cannot pick without reproduction.

**What would tip the decision:**
- **Hypothesis A confirmed (startup hang):** 30s manifests before the REPL prompt prints. Fix at `register_module_with_source` (add timeout) OR `wait_inmem_complete_blocking` (per-test guard) OR investigate why a module never reaches `inmem_done` (likely Decision 0030 cycle case).
- **Hypothesis B confirmed (macro-codegen wait on primitive):** 30s manifests when a slash-command argument triggers an unexpected macro expansion. Fix at `scheduler.rs::block_for_macro_codegen` to short-circuit on `Code::Primitive` (Decision 0048 invariant defence).
- **Hypothesis C confirmed (worker leak across tests):** 30s manifests only in batch test runs, not in standalone REPL. Fix at `CompilerSession::Drop` to enforce `shutdown()` (Principle 18 structural).

**Tipping evidence to gather:**
1. Run the 3-line repro at `tests/repl_info_primitives.rs` standalone — hang at REPL startup or at `/info`?
2. Enable `CRANELISP_SCHEDULER_TRACE=1` — is `wait_inmem_complete_blocking` parked? On what module?
3. Run the failing test in isolation vs in the full suite — does the hang only manifest under suite execution?

Outside /design's authority (requires source-level diagnosis). /dev (int) Wave 3 brief drives. The audit's contribution: rule out the wrong fix sites and name the right candidates each with Decision/Principle grounding.

### A-2 — `SlashCommand` public-or-private (architectural)

**Question.** Should `SlashCommand` be a public type (current facade) or remain a private lifetime-keyed enum (current source)? (See F-3.)

**What would tip the decision:**
- **Public:** A consumer outside int materialises (alternate REPL host, LSP, structured-output test harness). The source enum's `&'a str` shape is wrong (lifetime escape); the enum must own its data — non-trivial refactor.
- **Private:** No outside consumer ever materialises. The facade is wrong to name it public; demote to documentary.

The audit's recommendation in F-3 is to demote (private is correct under Principles 02 + 13). This is a binary the audit can make on its own grounds but flags here so /arch can override if a downstream commitment is pending.

### A-3 — `module_imports` ImportSpec recovery (S70+ structural)

**Question.** Should `SymbolTable::Import` retain the original parse-time `ImportSpec` (with alias, span, multi-name) as a sidecar, or should `module_imports` accept the degraded synthetic shape as canonical? (See F-11.)

**What would tip the decision:**
- **Retain sidecar:** An LSP / refactoring tool needs `module_imports` to return faithful parse-time data for "rename across imports" / "find usages." `SymbolTable` grows a per-module `Vec<ImportSpec>` sidecar. Principle 07: parse-time spec IS the single source of truth.
- **Accept degraded:** No such tool materialises; the degraded shape suffices for `/imports` slash-command display.

FIXME 0194's tail concern. /design (int) Wave 2 documents the degradation in the facade so consumers know; the structural decision is /arch's at S70 scope.

### A-4 — `Code::Primitive::ptr()` returning null vs panicking

**Question.** Should `Code::Primitive::ptr()` return `std::ptr::null()` (current — admits null-check discipline) or `unreachable!()` (panics — refuses to call ptr() on a non-callable code variant)? (See F-18.)

**What would tip the decision:**
- **Null (current):** call sites use a uniform `if c.ptr() == 0 { /* not callable directly */ }` filter; no panic on misuse. Aligns with Decision 0035 ("GOT is single source of truth; `ptr` lives in `SymbolTable.got()`") — `Code::Primitive::ptr()` returning null is the type-system encoding.
- **Unreachable:** call sites must pattern-match `Code` first; no fall-through possible. More aggressive Principle 18 enforcement but breaks the uniform `c.ptr() as i64` pattern at consumers.

/backend authority call (the `Code` enum lives in backend per Decision 0041). The audit notes it as adjacent because F-18 depends on the discipline holding.

---

## Verdict

**MEDIUM DRIFT — confirmed at the per-finding count, re-grounded in proportion.** The prior audit's "MEDIUM DRIFT not small" verdict was right in count but under-grounded in proportion: F-16 (per-FQ scheduler waits) is not a "both-move with facade marking deferral" finding — it is "source moves to land the settled per-FQ architecture; facade adds a subordinate deferral annotation." The Decision 0044 grounding + sequence-diagram grounding + open-FIXME grounding (0176 + 0179) make the facade target-stating, not over-prescribed. This is the load-bearing flip the re-author makes: **the per-FQ scheduler surface IS the architecture; the per-module current source is the as-built transitional shape.**

The drift is recoverable in Sprint 69's W2 + W3 — none of the findings forces a Decision register change — but the work is real:
- 6 facade-doc fires (F-1, F-3, F-6, F-7, F-8, F-15) + 4 partial / annotation tasks (F-11, F-16, F-18, F-19).
- 5–7 source-side narrowings (F-2, F-4, F-5, F-9, F-10) + F-17 diagnostic + repro + F-18 audit pass.
- The F-16 source-side delivery (per-FQ scheduler methods + `handle_gap` in `cluster.rs`) is multi-sprint: FIXME 0179 (cluster-mode read-union) → FIXME 0176 (Cluster-mode activation) → the five per-FQ methods → `handle_gap`. S69 W3 may complete 0179 + 0176; the per-FQ methods + handle_gap may stretch into S70.

The audit's main substantive corrections vs the prior version:
1. **F-16:** per-FQ waits are settled architecture (Decision 0044 + sequence diagrams), not over-prescribed facade. Source carries the migration; facade marks deferral.
2. **F-17:** rev3 hypotheses each map to a different architectural invariant (Decisions 0030, 0048, Principle 18 Drop). Correct fix site depends on which invariant is violated, not on pros/cons.
3. **F-9:** Principle 07 grounds the disposition as binary, not split-the-difference. Duplication is the defect; consolidation is the fix.
4. **F-4:** the `CLAUDE.md §"String Newtypes"` hard rule (+ Principle 18) is the binding, not stylistic preference.
5. **14 of 18 confirmed dispositions** gain explicit Decision/Principle/FIXME grounding that the prior audit lacked.

The diagnostic step for rev3 (3-line repro + scheduler trace + standalone-vs-suite split) is the durable next move and must produce a committed test per the failing-not-ignored discipline. The corresponding architectural-invariant defence (whichever of Decision 0030, Decision 0048 §"backend dep-ban", or Principle 18 Drop-discipline applies) is the structural landing, not a band-aid.
