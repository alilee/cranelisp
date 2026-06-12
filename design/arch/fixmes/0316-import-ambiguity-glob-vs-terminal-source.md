---
number: 0316
target: /spec
filed_by: /sprint
filed_at: 2026-06-12
sprint_filed: 78
refers_to: spec/08-modules.md §8.6.4 (Conflict Rules — "same original definition NOT ambiguous"), src/imports.rs insert_detecting_ambiguity, design/arch/fixmes/0312 (resolved), S78 Wave 6
status: open
---

# Reconsider the import-ambiguity model: terminal-source dedup + whether globs should be ambiguity-protected

## Issue (surfaced by S78 Wave 6, noted not fixed — user-directed)

Two related gaps in how import-name conflicts are decided:

1. **Immediate-source vs terminal-source dedup (spec-conformance gap).**
   `src/imports.rs::insert_detecting_ambiguity` keys the "same-source dedup"
   on the **immediate** `source.module`, not the **terminal** original
   definition. So a glob `(import [primitives [*]])` (immediate source
   `primitives`) + a specific `(import [fn.option [Option]])` where `fn.option`
   **re-exports** `primitives/Option` (immediate source `fn.option`) read as TWO
   sources → `Ambiguous`, even though both resolve to the SAME original
   definition (`primitives/Option`). Spec §8.6.4 says *"Same-source duplicates
   (the same name arriving through two re-export paths from the same original
   definition) are NOT ambiguous"* — which requires chain-following BOTH sides to
   their terminal home before comparing. The impl compares immediate sources, so
   a re-export does NOT dedup a glob+specific overlap. (S78 Wave 6 worked around
   this in stdlib by dropping the redundant specific imports; user code hitting
   the same shape — glob a module + specifically import a name it re-exports —
   would hit the same false collision.)

2. **Is protecting globs the right strategy? (user, 2026-06-12).** Open design
   question: should a name brought by a `[*]` glob participate in hard ambiguity
   the same way a *specific* named import does? Candidate alternatives to the
   current "all explicit imports are peers; any same-name overlap collides":
   a specific import could *shadow* a glob-brought name (wildcard < explicit,
   the Java model — earlier raised + then deferred in S78); or glob-brought names
   could be a lower-precedence tier that only collide glob-vs-glob. The S78
   ruling was "overlapping imports MUST collide" (footgun protection) for
   genuinely-different types; once the two `Option`s became one (Wave 6
   re-export), the remaining collisions are same-terminal-source, which (1)
   says should dedup anyway. The user flagged that the broader glob-protection
   strategy is "not clearly right" and worth revisiting.

## Proposed resolution

`/spec` (with `/arch`) decides the import-ambiguity model holistically:
- Whether §8.6.4 same-source dedup is **terminal-source** (chain-follow both
  sides) — if so, `insert_detecting_ambiguity` gains a terminal-resolve before
  the `Ambiguous` verdict (an int change), and a re-export silently dedups.
- Whether glob `[*]` imports are **peers** of specific imports (current) or a
  **lower-precedence tier** (specific shadows glob; glob-vs-glob still collides).
These interact — e.g. terminal-source dedup may make most real glob+specific
overlaps benign without a precedence tier. Pick a coherent model + cascade to
§8.6.4/§8.6.5 + `insert_detecting_ambiguity`.

## Related finding — the prelude-fallback retry is duplicated 5× (target /arch, fold into this review)

Surfaced post-close (user, 2026-06-12) while reflecting on why the S78 §2
prelude-fallback regression needed ~4 separate fix sites. **All bare-name
resolution paths DO route through one primitive — `cranelisp_types::resolve()`
(`crates/cranelisp-types/src/resolve.rs:260`)** — but the *prelude outer-scope
retry* layered on top of it is hand-rolled at **5 sites**, because `resolve()`
is deliberately data-only and cannot see the session-side `prelude_fallback`
bit. The identical 3-step wrapper (resolve in current view → on miss, if the
module's bit is ON, resolve again rooted at `prelude` → public-only I-1 filter)
repeats in:
- `checker.rs:880` `resolve_current_or_prelude` (value/type)
- `checker.rs:1219` `probe_current_or_prelude` (entry/scheme)
- `checker.rs:1345` `resolve_entry_in_current_module` (ctor value+pattern, internal-gate)
- `checker.rs:1392` `resolve_terminal_entry_or_prelude` (trait-method)
- `src/expander.rs:289` `recognize_macro_head` (macro head — **a different crate**, duplicates the whole thing)

This fragmentation is *why* the "fallback wired for path X not Y" gap recurred
4× across S78 (value/type/ctor → trait [0315] → macro-head → ctor gates [0317]).

**Proposed unification (for /arch — touches `cranelisp-types`, /arch-only):** a
`resolve_with_fallback(symbol_tables, module_aliases, first_hop_view,
current_module, name, fallback_on: bool, prelude_path, span)` in
`cranelisp-types`. Passing the *already-looked-up* bit as a plain `bool` (caller
does its own `prelude_fallback.get(module)`) + the prelude `ModuleFullPath`
(a types-owned type) keeps types data-only — **no reverse dependency** on
typecheck's `PreludeFallback`. Collapses all 5 bespoke wrappers (incl. the
cross-crate expander one) to a single seam; visibility filtering moves in too
(data-layer already). Makes any future bare-name path get the fallback for free
instead of re-deriving it. NOT blocking; evaluate alongside the ambiguity-model
decision since both touch the module-traversal primitives. See
`memory/feedback_thread_cross_cutting_at_one_seam.md`.

## Operational implication / Context

NOT blocking — S78 closed with stdlib green (overlaps removed) and the language
rule as ruled (overlaps collide). This is a deliberate future design item the
user asked to NOTE rather than fix at close. No test is red on it. FIXME 0312
(the stdlib root-cause, target /design) is resolved by Wave 6; its residual
design question is relocated here.
