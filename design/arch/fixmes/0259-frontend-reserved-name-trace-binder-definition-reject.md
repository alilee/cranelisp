---
number: 0259
target: /dev (frontend)
filed_by: /arch
filed_at: 2026-06-04
sprint_filed: 76
refers_to: design/arch/tracing.md §3.1, design/arch/principles/10-parser-keywords-distinct-syntax.md, crates/cranelisp-frontend/src/ast_builder.rs (build_let_bindings, the defn-name path, build_fn params), design/arch/fixmes/0257-spec-trace-all-modes-nested-error-keyword-consistency.md §4d
status: open
---

# Reject `trace` in binder/definition positions — root-special-form reserved-name enforcement

## Issue

The 2026-06-04 user ruling makes `(trace …)` a **root special form** (Principle 10's two-category
amendment; `design/arch/tracing.md` §3.1 / §2.4). A root special form's name is **reserved**: user
code MUST NOT define or bind it. The as-built compiler does NOT enforce this.

`build_form` (`ast_builder.rs:991`) matches the head symbol `"trace"` only in **head** position, so the
name `trace` appearing as:

- a `defn` name argument — `(defn trace [x] …)`
- a `let` binder — `(let [trace 1] …)`
- a `fn` / lambda parameter — `(fn [trace] …)`
- any other binder/definition position

flows through `expect_symbol` (`build_let_bindings:1185`, the defn-name path, the `build_fn` param
path) with **no reserved-word check** and is silently accepted-and-shadowed. Per the ruling this must
be **rejected outright** (not allowed-but-shadowed). User-accepted cost — a user cannot name a
function/binding `trace`.

## Proposed resolution

1. Add a reserved-name check to the AST builder's binder/definition paths. When a binder or definition
   position would bind the name `trace`, return a parse error (e.g. `"'trace' is a reserved special-form
   name and cannot be defined or bound"`) at the offending symbol's span. The hit set is every
   `expect_symbol` call that introduces a *binding* (not a *reference*):
   - `build_let_bindings` (`:1185`) — let binder names.
   - the `defn` name argument path (`build_defn_variant` / the defn entry point).
   - `build_fn` / lambda parameter names (`:1228`+).
   - `match` pattern variable binders if they can introduce `trace` as a fresh binding (confirm whether
     a pattern var named `trace` should also be rejected — `/arch`'s read: yes, it is a binder; but a
     constructor/field name is not a binder, so leave those alone).
   The reference position (`trace` as the head of a form) is the special-form dispatch and is correct
   as-is — do NOT reject `trace` there.

2. A single shared helper (e.g. `reject_reserved_binder_name(sym, span)`) keeps the rule single-sourced
   (Principle 7) rather than copy-pasted at each binder site. If/when other root special forms need the
   same guard, the helper's reserved set is the one place to extend — though today the structural special
   forms (`defn`, `let`, `if`, `match`, …) already cannot reach a binder position as a bound *name*
   because the parser dispatches them in head position; `trace` is the case that slips through because it
   can appear as a plain symbol in a binder slot. Scope the helper to what the ruling requires (`trace`);
   do not speculatively expand the reserved set beyond what is needed (Principle 6).

3. Add unit tests inside the frontend crate: `(defn trace [x] x)`, `(let [trace 1] trace)`,
   `(fn [trace] trace)` each produce a parse error; `(trace (f 1))` in head position still builds an
   `Expr::Trace`. (Per the unit-tests-with-dev rule — `/qa`'s integration coverage is FIXME 0258 +
   0257's note; the in-crate unit tests are this FIXME's.)

4. Update the stale `build_trace` comment (`:1014`–`:1024`) that documents the now-retracted `--link`
   missing-symbol rejection — `(trace …)` works in all modes now (`tracing.md` §2.5). This is a paired
   cleanup; the substantive enforcement is items 1–3.

5. Regenerate `crates/cranelisp-frontend/public-api.txt` if the surface changed (likely not — the helper
   is internal). Fix any warnings the change introduces.

## Operational implication / Context

Small, self-contained frontend change. Independent of the heavier trace-runtime relocation FIXMEs
(0254 intrinsics, 0255 backend, 0256 int) — it touches only the AST builder's binder paths and can land
in any wave (does not depend on the runtime relocation). It is the implementation owner for FIXME 0257
§4d's normative binding-rejection statement, so it should land with or after the /spec §2 grammar +
binding-rejection text so the spec and the enforcement agree. Sequencing is **/sprint + user's call**.
