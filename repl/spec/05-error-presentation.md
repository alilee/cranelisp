> [REPL specification index](index.md)

## 5. Error Presentation [Tested]

### 5.1 Error Format [Tested]

All errors MUST display:

1. The error category (parse error, type error, etc.) [Tested tests/repl_negative::type_error_arg_mismatch]
2. The source location (file/line/column or character span) [Tested tests/repl_negative::type_error_arg_mismatch]
3. A human-readable message [Tested tests/repl_negative::type_error_arg_mismatch]

Errors MUST be written to stdout (as part of the REPL conversation flow, visible in piped output and the showcase). Stderr is reserved for traces and diagnostic output. Errors MUST NOT crash the REPL session — the user MUST be able to continue entering expressions after any error. [Tested+Neg tests/repl_negative::type_error_arg_mismatch, tests/repl_negative::type_error_neg_stderr_empty_and_session_survives]

### 5.2 Error Recovery [Tested]

After any error (parse, type, runtime), the REPL MUST:
- Display the error [Tested tests/repl_introspection::sig_unknown_name_graceful]
- Reset input state (clear any partial multi-line input)
- Present the prompt for new input

The session state (defined functions, types, modules) MUST NOT be corrupted by an error in a subsequent expression. [Tested+Neg tests/repl_introspection::sig_unknown_name_graceful]

### 5.3 Type Error Quality [Tested]

Type errors MUST include:
- The expected type (fully qualified) [Tested tests/repl_negative::type_error_names_expected_type_fully_qualified]
- The actual (inferred) type (fully qualified) [Tested tests/repl_negative::type_error_arg_mismatch] [Tested tests/repl_negative::type_error_names_actual_type_fully_qualified]
- The source location of the mismatch [Tested tests/repl_negative::type_error_has_source_location]

Type errors SHOULD suggest common fixes when applicable.

### 5.4 Reader-Level Diagnostics Are Self-Documenting [S114]

The self-documenting-REPL principle ([root CLAUDE.md, Design Principles](../../CLAUDE.md#design-principles)) reaches
below type checking to the **reader** itself: a malformed lexical or grammatical
construct MUST produce a **located, self-documenting** error, never a silent
degradation to a different-but-valid form and never an opaque internal failure.
The reader is the first thing a new user's mistakes hit, so its diagnostics are
part of the experience contract. Two reader-level malformations are load-bearing
here — both settled in the language spec, both surfaced at the prompt:

- **Dangling module qualifier.** A `/` paired with an **empty half** — an empty
  local half (`foo/`, `a.b/`), or the symmetric empty module half (`/bar`) — is a
  **located compile-time error at the offending token, in every position** (value,
  call head, operand, annotation, type). It MUST NOT silently degrade to the
  module-less name (`foo`) or the bare local name (`bar`), and MUST NOT pass
  through as a literal symbol. The message MUST name what a qualified name
  requires (a non-empty module on the left of the `/` and a local name on its
  right) and MUST distinguish this from bare-`/` division, so the fix is
  unambiguous. (Language spec: [`spec/08-modules.md §8.5.1`](../../spec/08-modules.md),
  [`spec/02-grammar.md §2.4`](../../spec/02-grammar.md).) [S114]

- **Annotation reader macro `:` — whitespace-tolerant, form-binding.** The `:Type`
  introducer is a `^`-style reader macro that **binds the immediately-following
  form**; because it reads that following form, **whitespace between `:` and it is
  permitted** — `: Int` is the same annotation as `:Int`, and `: (Fn [a] a)` the
  same as `:(Fn [a] a)`. The two spellings MUST resolve identically (same value,
  same type, same fully-qualified display); a space MUST NOT change the reading.
  (Language spec: [`spec/01-lexical.md §1.4.5`](../../spec/01-lexical.md),
  [`spec/02-grammar.md §2.3.8`](../../spec/02-grammar.md).) [S114]

- **Dotted or qualified name in a binder position is rejected, locatedly.** Both
  forms of qualification — a module qualifier (`mod/name`) and a dotted path
  (`a.b`) — are **reference** syntax: they reach across modules, and both are
  legal wherever a name is *read*. Neither is legal where a name is *introduced*.
  A **binder** names a new name in the current module (or lexical scope), so it
  never carries either. A qualified **or dotted** spelling in any binder position
  (a definition head — `defn`, `def`, `deftype`, `deftrait`, `defmacro`, `const`
  — or a `let` binder) is a compile-time error with the span **on the offending
  binder name**, and the message MUST say what to write instead (the bare name)
  — the REPL never silently coins a name into another module. The dotted case
  MUST additionally say why `.` cannot appear there (it is reserved for
  type/trait qualification), because a user who writes `(defn a.bar …)` is
  usually reaching for a namespace, not a typo. (Language spec:
  [`spec/05-definitions.md §5`](../../spec/05-definitions.md),
  [`spec/04-expressions.md §4`](../../spec/04-expressions.md),
  [`spec/08-modules.md §8.5.1`](../../spec/08-modules.md).) [S115]

  The reference/binder boundary is the whole of the rule, and it is symmetric:
  the same spelling that is rejected as a binder MUST resolve as a reference when
  a name by that path exists. `(collections.vec/count (vec 1 2 3))` is an
  ordinary call; `(defn a.bar [x] x)` is an error. A conforming REPL demonstrates
  both sides — a reject alone teaches "`.` is forbidden", which is false.

These reader diagnostics are exercised end-to-end in the `06-modules` showcase
demo (dangling `/bar` **and** `foo/`, the `(collections.vec/count …)` legal
dotted reference paired with the `(defn foo/bar …)` and `(defn a.bar …)` /
`(let [a.b 1] …)` binder rejects, and `: Int` ≡ `:Int` tolerance) as replayed
sentinels. Both dangling-qualifier halves now report at parity — each names which
half is missing and how to fix it. One residual remains: the **degenerate
no-form-to-bind spelling**, where `:Int` alone reports `annotation missing
expression` but the spaced `: Int` alone reports `undefined variable: :` — the
space defeats the reader macro in exactly the position where §5.4's second bullet
promises it does not matter. That case is tracked with the rest of the `:`-fold
seam (FIXME 0708); the requirement above is on the **located +
self-documenting + no-silent-degradation** contract, which holds for every case,
not on any single message's exact prose. [S115]

### 5.5 Compiler-Stage Diagnostics Name User-Facing Subjects [S119 — FIXME 0915]

§5.4 carried the self-documenting contract *down* to the reader. This section
carries it *up* to the stages a user never names: monomorphisation, code
generation, linking. A failure there is rare, but it is exactly the moment a
user has least to go on, so the diagnostic MUST stay inside the vocabulary the
prompt itself can explain. Three requirements, each independent of any
particular failure's cause:

- **Located at the user's form.** A compiler-stage error MUST carry the span of
  the form the user typed, per §5.1's location MUST. A degenerate `0..0` span
  satisfies the letter of "a character span" and none of its purpose: it points
  at nothing, and on a multi-form line the user cannot tell which form failed.
  Where the failing artifact is a synthesised body with no source of its own,
  the span MUST be the *triggering* user form, not the artifact's.

- **The subject is named as the user would write it.** The compilation subject
  in the message MUST be a name the user can type back at the prompt. Internal
  synthetic names (`__expr` and the `__macro_*` family), monomorphisation
  instance mangles (`name$Param+Param`), and doubled module prefixes
  (`user/user/name`, arising when a module path is prepended to a symbol that
  already carries one) MUST NOT appear. A REPL expression's subject is the
  expression; a monomorphised instance's subject is the generic definition the
  user defined, and the instantiating types belong in the prose if they are
  load-bearing.

- **Every noun in the message is discoverable, or is rephrased.** The
  self-documenting principle ([root CLAUDE.md, Design Principles](../../CLAUDE.md#design-principles)) makes this
  binary: if the message's central noun is a type or constructor, then typing
  that name — or `/info` on it — MUST describe it. A message whose subject the
  REPL itself answers with `undefined variable` / `unknown symbol` is not
  actionable at any level of user skill, because the one investigative move
  available at the prompt fails. Where a name is genuinely internal and cannot
  be made discoverable, the message MUST be rephrased around what the user
  *wrote* instead of what the compiler *built*.

Nested stage wrappers MUST NOT repeat a category-and-span prefix that an outer
wrapper already emitted (`codegen error at 0..0: codegen failed for X: codegen
error at 0..0: …`); one located category prefix per diagnostic.

These are requirements on the diagnostic *frame*, not on any stage's ability to
succeed — a refusal a stage genuinely cannot avoid is still a conforming
refusal once it is located, subject-named, and phrased in discoverable nouns.
