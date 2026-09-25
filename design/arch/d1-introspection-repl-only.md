# D1 — Introspection is REPL-only; compile data lives on the symbol table

**Status: current cross-context contract, delivered.** The user ratified the
direction in Sprint 80. Introspection is a REPL display facility owned by the
Binary/int context
([BC 6](bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle)); the
compile pipeline reads nothing from it. The one compile-necessary datum it used
to hold — a macro's original form — lives on the symbol table.

## 1. Why compile data is not introspection

- Introspection holds uniform, per-`FQSymbol` REPL display data: source text,
  the displayed Sexp, expansion and CLIF text. One int-side record serves every
  definition kind, so no lifecycle variant carries its own display fields.
- A compile-path read of that record made batch correctness depend on a REPL
  facility, and populating it in every mode erased the REPL/batch signal. The
  cure was to move the compile datum, not to make introspection always on.
- **Only macros carry their form on the symbol table.** A macro declaration has
  no checked body (`ast`) to carry its compile input — its clause bodies are
  separate entries — so the form has nowhere else to live. Do not add generic
  source or Sexp fields to other lifecycle records; their compile input is
  their body.
- Serialising the whole introspection record into the cache is rejected: it
  would mix display concerns into the cache and raise invalidation questions
  for data no compile needs.

## 2. Where the macro form lives

- `MacroDeclaration.macro_sexp` (`crates/cranelisp-types/src/lifecycle.rs`) is
  the macro's original `defmacro` form.
- It is serialised with the table, so a cache-restored macro carries its form
  and clause recompilation needs no rehydration from introspection.
- Registration writes it unconditionally in every mode.

## 3. Introspection exists only in the REPL

- **The store is absent outside the REPL.** `SharedState.introspection` is an
  `Option` built from `RunMode::populates_introspection()` at session
  construction: present under `Repl`, `None` under `--run` and `--link`. The
  store's existence and its population share one carrier (§4).
- **Readers are REPL-only by call path.** The read accessors
  `symbol_source`, `symbol_sexp` and `symbol_clif`, and `get_introspection`
  behind `/source`, `/info` and agent harvest, treat an absent store or record
  as "no record". Test discovery, tracing, `--link` artefact routing and cache
  restoration never read it. **A compile-path read of introspection is a
  defect.**
- **Source regeneration falls back to the symbol table.** REPL persistence
  reads verbatim input from introspection and falls back to
  `MacroDeclaration.macro_sexp` for a macro without a record, such as one
  restored from the cache.
- **Codegen byproducts follow their cost.**
  - `code_size` is free: codegen returns it in every mode, and int retains it
    only when the store exists.
  - CLIF text exists only for introspection: int asks backend to capture it
    only when the store exists (`capture_clif`).
  - Native disassembly is never stored; `cranelisp_backend::produce_disasm`
    derives it on demand for `/disasm`.

## 4. The run-mode carrier

`RunMode` (`src/session_v4/types.rs`) records which CLI verb launched the
session: `Repl`, `Run` or `Link`. It has two consumers:

- `populates_introspection()` decides the introspection store (§3);
- `is_repl()` is the platform layout-hash gate's discriminator: the REPL warns
  and loads on drift, `--run` and `--link` refuse.

Rules:

- **The mode is an explicit carrier, never inferred** from the store's presence
  or any other proxy. A store's presence does not state intent, and inferring
  mode from it is what produced the original defect.
- **`RunMode` is int-internal.** Frontend, typecheck and backend never see it,
  so it does not belong in `cranelisp-types`
  ([Principle 15](principles/15-facade-types-live-with-behavior.md)).
- **It selects no codegen strategy.** JIT versus object emission is decided by
  the Cranelift module the caller supplies
  ([module caching](../backend/module-caching.md) §5), not by run mode.

## 5. Public boundary

- The only cross-crate element is `MacroDeclaration.macro_sexp`; it follows the
  types cache contract
  ([types memory](../../crates/cranelisp-types/CLAUDE.md#the-serde-shape-is-the-cache-contract)).
- `Introspection`, `SharedState` and `RunMode` are int-internal.
- The backend's CLIF capture flag is an ordinary parameter of its codegen
  entry; its presence does not make introspection a backend concept.
