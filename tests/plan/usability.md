# Usability Register

Structured destination for findings from user-proxy skills. When `/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, or `/platform` encounter corner cases, unhelpful errors, inference friction, missing APIs, or ergonomic issues, they file findings here rather than routing ad-hoc to individual compiler skills. `/qa` triages findings and routes them to the responsible skill.

**Blocking findings are part of the ring gate** -- a ring cannot advance if any blocking usability finding remains unresolved.

---

## Filing Process

1. **User-proxy skill encounters friction** while exercising the language from their perspective (library author, learner, documentation writer, application developer, interactive user, extension author).
2. **Skill files a finding** in the appropriate ring section below, using the template.
3. **`/qa` triages** the finding: assigns severity, identifies the responsible compiler skill, and adds it to the ring gate checklist.
4. **Responsible skill addresses** the finding (fix, workaround, or reasoned deferral).
5. **`/qa` verifies** the resolution and marks the finding as resolved, recording the ring and commit.

---

## Filing Template

Each finding includes:

| Field | Description |
|---|---|
| **ID** | `U{ring}.{seq}` -- e.g. `U0.1`, `U2.3` |
| **Source skill** | Which user-proxy skill encountered it (`/stdlib`, `/examples`, `/docs`, `/port`, `/repl`, `/platform`) |
| **Category** | One of: `error quality`, `inference friction`, `missing API`, `performance`, `ergonomics`, `discoverability`, `other` |
| **Severity** | `blocking` (must fix before ring advance), `important` (should fix), `deferred` (nice to have) |
| **Description** | What happened, what was expected, what would be better |
| **Responsible skill** | Which compiler skill should address it (if known) |
| **Status** | `open`, `in-progress`, `resolved`, `wont-fix` |
| **Resolution** | How it was resolved, with ring and commit reference |

### Who Contributes

| Skill | Perspective | Typical Findings |
|---|---|---|
| `/stdlib` | Library author | Missing primitives, awkward trait APIs, naming surprises |
| `/examples` | Learner | Confusing errors, non-obvious syntax, missing affordances |
| `/docs` | New user advocate | Learning curve gaps, terminology inconsistencies |
| `/port` | Application developer | Scale issues, module friction, stdlib gaps, IO model limits |
| `/repl` | Interactive user | Discoverability gaps, feedback quality, latency |
| `/platform` | Extension author | C-ABI awkwardness, marshalling pain, IO model leaks |

### What Gets Registered

- Corner cases where language behavior is surprising or unintuitive
- Unhelpful or misleading error messages
- Type inference that requires too many annotations
- Missing stdlib functions that real code needs
- Macro system limitations encountered in practice
- REPL experience gaps (discoverability, feedback, performance)
- Module system friction (import patterns, visibility surprises)
- Performance problems at realistic scale
- Platform/FFI ergonomic issues

---

## Ring 0: Core

*No findings yet.*

---

## Ring 1: Heap

### U1.1 — Missing string primitives for text/string.cl

| Field | Value |
|---|---|
| **ID** | U1.1 |
| **Source skill** | `/stdlib` |
| **Category** | `missing API` |
| **Severity** | `important` |
| **Description** | Ring 1 provides 8 string primitives (`str-concat`, `str-eq`, `str-len`, `string-identity`, `int-to-string`, `float-to-string`, `bool-to-string`, `parse-int`). The stdlib plan for `text/string.cl` requires 11 additional operations: `substring`, `char-at`, `split`, `join`, `replace`, `trim`, `starts-with?`, `ends-with?`, `contains?`, `to-upper`, `to-lower`. These are straightforward to implement as extern primitives in `cranelisp-runtime` (Rust's `str` methods), but they do not exist yet. Not needed for Ring 2 foundation modules (Eq, Display, Option, Result, assertions), but needed for `text/string.cl` (Phase 2, module 9 in build order). |
| **Responsible skill** | `/backend` (runtime primitives), `/platform` (runtime crate) |
| **Status** | `open` |
| **Resolution** | — |

### U1.2 — parse-int type mismatch (returns Int, should return Option Int)

| Field | Value |
|---|---|
| **ID** | U1.2 |
| **Source skill** | `/stdlib` |
| **Category** | `missing API` |
| **Severity** | `important` |
| **Description** | `parse-int` is declared as `(Fn [String] Int)` in the type system but actually returns `Option Int` at runtime (tag 0 = None, heap [tag=1, n] = Some). Two integration tests are `#[ignore]` (`parse_int_valid`, `parse_int_invalid`). The type mismatch means no Cranelisp code can safely use `parse-int` — the return value cannot be matched as an Option. Fix requires either: (a) expressing `(Option Int)` as a return type referencing the user-defined Option ADT (needs module system, Ring 2), or (b) a compiler-seeded Option in primitives (conflicts with optional prelude principle). Recommend option (a), fixing in Ring 2 when modules are available. |
| **Responsible skill** | `/typecheck` |
| **Status** | `open` |
| **Resolution** | — |

### U1.3 — Nested heap ADT RC not directly tested

| Field | Value |
|---|---|
| **ID** | U1.3 |
| **Source skill** | `/stdlib` |
| **Category** | `ergonomics` |
| **Severity** | `important` |
| **Description** | The stdlib needs nested heap ADTs like `(List (Option Int))`, `(Option String)`, and `(List String)`. While `string_in_adt` tests `(Some "hello")`, there are no tests for deeper nesting (e.g., a List of Strings, or an Option containing an ADT containing a String). If drop glue does not recursively decrement nested heap fields, stdlib data structures will leak memory. The RC machinery is designed to handle this, but explicit test coverage is needed to build confidence before stdlib development begins. |
| **Responsible skill** | `/qa` |
| **Status** | `open` |
| **Resolution** | — |

### U1.4 — No auto-generated field accessors for ADTs

| Field | Value |
|---|---|
| **ID** | U1.4 |
| **Source skill** | `/stdlib` |
| **Category** | `ergonomics` |
| **Severity** | `deferred` |
| **Description** | Ring 1 ADTs require `match` for all field access: `(match p [(Point x y) x])` instead of `(Point.x p)` or a generated accessor function `x :: (Fn [Point] Int)`. The sketch had auto-generated dotted field accessors. Without them, stdlib code for types like Option, Result, Pair is more verbose (3-line match instead of 1-line call). Not a capability blocker — all stdlib functions can be written using `match` — but it increases code volume and reduces readability, especially for simple field extraction. The stdlib plan's build order does not depend on accessors. |
| **Responsible skill** | `/typecheck` |
| **Status** | `open` |
| **Resolution** | — |

### U1.5 — Closure capturing heap types (String, ADT) not tested

| Field | Value |
|---|---|
| **ID** | U1.5 |
| **Source skill** | `/stdlib` |
| **Category** | `ergonomics` |
| **Severity** | `important` |
| **Description** | Ring 1 closure tests capture Int and Bool values, and closures return ADTs, but no test exercises a closure that *captures* a String or an ADT with heap fields. Example: `(let [s "hello"] (fn [] (str-len s)))` — the closure captures a heap-allocated String. If RC handling for captured heap values is incorrect (e.g., not incrementing on capture, or not decrementing on closure drop), stdlib higher-order functions over strings and ADTs will leak or crash. The patterns `(fn [opt] (match opt [(Some x) (f x) None default]))` where `default` is a captured String are fundamental to Option/Result combinators. |
| **Responsible skill** | `/qa` |
| **Status** | `open` |
| **Resolution** | — |

### U1.6 — REPL type variable names for polymorphic ADTs are internal, not source-level

| Field | Value |
|---|---|
| **ID** | U1.6 |
| **Source skill** | `/docs` |
| **Category** | `ergonomics` |
| **Severity** | `important` |
| **Description** | When displaying polymorphic ADT values at uninstantiated type parameters, the REPL shows internal type variable names (e.g., `:(Option t1) None`) rather than source-level names from the type definition (e.g., `:(Option a) None`). This is visible in the `repl_adt_sum_none` test, which uses a flexible assertion (`display.contains("Option") && display.ends_with("None")`) rather than checking for an exact match. When writing documentation and tutorial content for beginners, REPL transcripts cannot be written deterministically because the variable name is unpredictable. A beginner who defined `(deftype (Option a) ...)` and then sees `t1` in the output would be confused. The REPL display should normalize type variables to match the source-level names from the type definition, or at minimum use consistent alphabetic naming (`a`, `b`, `c`). |
| **Responsible skill** | `/backend` or `/typecheck` (owner of `format_result_value`) |
| **Status** | `open` |
| **Resolution** | -- |

### U1.7 — Error messages for Ring 1 type mismatches are untested for quality

| Field | Value |
|---|---|
| **ID** | U1.7 |
| **Source skill** | `/docs` |
| **Category** | `error quality` |
| **Severity** | `important` |
| **Description** | Ring 1 error path tests in `tests/ring1.rs` use empty substring matching (e.g., `assert_type_error(src, "")` and `assert_error(src, "")`). This confirms that an error occurs but does not verify the content of the error message. From a documentation perspective, the error catalog (`user/errors/type-errors.md`) needs to show users what actual messages look like, but there is no tested guarantee of message quality. Specific cases: (1) passing String where Int expected (`add-i64 "hello" 1`), (2) wrong constructor arity (`Point 1` when Point takes 2), (3) if-branch type mismatch between String and Int, (4) closure arity mismatch, (5) undefined constructor reference. Each of these should produce an error message that names both the expected and actual types. Without tested message content, documentation may not match what users actually see. |
| **Responsible skill** | `/qa` (test coverage), `/typecheck` (message content) |
| **Status** | `open` |
| **Resolution** | -- |

### U1.8 — Product type field accessors not exercised in Ring 1

| Field | Value |
|---|---|
| **ID** | U1.8 |
| **Source skill** | `/docs` |
| **Category** | `discoverability` |
| **Severity** | `deferred` |
| **Description** | Spec section 5.2.6 specifies that `deftype` auto-generates accessor functions for each named field (e.g., `(x (Point 3 4))` returns `3`). No Ring 1 integration test exercises this path. The getting-started guide and tutorial curriculum teach only the `match`-based approach for field extraction because it is the tested path. If accessors work, they provide a significantly simpler pattern for beginners (`(x p)` vs. `(match p [(Point x y) x])`). The documentation should teach both approaches once accessor availability is confirmed. This overlaps with U1.4 (filed by `/stdlib`) but is filed separately because the documentation impact is distinct: it affects the learning path and tutorial design. |
| **Responsible skill** | `/qa` (test), `/typecheck` (implementation) |
| **Status** | `open` |
| **Resolution** | -- |

### U1.9 — Polymorphic ADT field display shows raw pointer for heap-typed fields

| Field | Value |
|---|---|
| **ID** | U1.9 |
| **Source skill** | `/repl` |
| **Category** | `ergonomics` |
| **Severity** | `important` |
| **Description** | When a polymorphic ADT contains a heap-typed field through a type variable (e.g., `(Some "hello")` where `Some` is defined as `(Some [:a val])`), the REPL displays the raw pointer value instead of the formatted string: `:(Option String) (Some 40383875776)` instead of the expected `:(Option String) (Some "hello")`. This happens because `format_adt_heap_value` reads field types from `TypeDefInfo`, which stores them as `Type::Var(a)` (the declared type parameter), not as the concrete instantiated type `Type::String`. The concrete type args are available in the `Type::ADT(name, type_args)` value but are not substituted into the field types before formatting. Monomorphic ADTs with concrete field types (e.g., `(deftype Named [:String name])`) display correctly. The fix requires `format_adt_heap_value` to build a substitution map from `type_params` to `type_args` and apply it to each field's type before calling `format_field_value`. This affects all polymorphic ADTs with heap-typed fields (String, nested ADTs, closures). The type display portion `:(Option String)` is correct — only the value display is affected. |
| **Responsible skill** | `/qa` or `/backend` (owns `format_result_value` in `src/repl.rs`) |
| **Status** | `open` |
| **Resolution** | -- |

### U1.10 — Vec is the critical-path blocker for application-scale programs

| Field | Value |
|---|---|
| **ID** | U1.10 |
| **Source skill** | `/port` |
| **Category** | `missing API` |
| **Severity** | `important` |
| **Description** | The Sudoku Solver exemplar requires `Vec` in 5 of 7 Cranelisp modules: `Grid` stores 81 cells as `:(Vec Cell)`, candidates need a collection type, `peers` returns indices, HTML generation iterates over cells, and form parsing produces a collection of values. Without Vec, none of these modules can be composed into a working program, even though Cell/SolveResult ADTs, string helpers, and closure patterns are individually expressible at Ring 1. Vec is deferred to Sprint 3 (Chunk D). This is intentional, but it means application-scale validation is blocked until Sprint 3. Recommend Vec be the highest-priority item in Sprint 3 to unblock both `/port` and `/stdlib` collection modules. |
| **Responsible skill** | `/arch` (scheduling), `/backend` + `/platform` (implementation) |
| **Status** | `resolved` |
| **Resolution** | Sprint 3: Vec delivered with `vec-get`, `vec-set`, `vec-push`, `vec-len`. 32 integration tests + 4 REPL tests passing. Grid data model and solver algorithm now expressible. String primitives (U1.1) are the new critical path for full exemplar. |

### U1.11 — Deeply nested str-concat is ergonomically painful for string-building

| Field | Value |
|---|---|
| **ID** | U1.11 |
| **Source skill** | `/port` |
| **Category** | `ergonomics` |
| **Severity** | `deferred` |
| **Description** | Building HTML strings at Ring 1 requires deeply nested `str-concat` calls: `(str-concat "<td>" (str-concat content (str-concat "</td>" "")))`. A single HTML table cell with a class attribute requires 5+ levels of nesting. The exemplar's `html.cl` module (~250 lines) will be dominated by `str-concat` nesting. Mitigations arrive at Ring 3 (threading macros `->`, string interpolation macros) but the core experience of building strings from parts is a known pain point. A variadic `str` primitive (like Clojure's `str`) accepting multiple arguments would help even without macros. Not a blocker -- the code works -- but it is a real ergonomic cost. |
| **Responsible skill** | `/stdlib` (variadic `str`), `/frontend` (threading macros at Ring 3) |
| **Status** | `open` |
| **Resolution** | -- |

### U1.12 — Vec primitives not registered in typechecker symbol table

| Field | Value |
|---|---|
| **ID** | U1.12 |
| **Source skill** | `/qa` |
| **Category** | `missing API` |
| **Severity** | `blocking` |
| **Description** | Vec primitives (`vec-get`, `vec-set`, `vec-push`, `vec-len`) are not registered in the typechecker's symbol table. The backend has inline codegen for them (`vec_codegen.rs`), the runtime has implementations (`vec.rs`), and the frontend parses `VecLit`, but the typechecker reports "undefined variable: vec-get" etc. These primitives are polymorphic (e.g., `vec-get :: (Fn [(Vec a) Int] a)`), unlike the Ring 1 string primitives which are monomorphic and registered via `ring1_primitives()`. The vec primitives need to be registered with polymorphic type schemes. 33 Vec integration tests and 10 Vec RC tests are `#[ignore]` in `tests/ring1.rs` and `tests/rc.rs` waiting on this fix. |
| **Responsible skill** | `/typecheck` |
| **Status** | `resolved` |
| **Resolution** | Sprint 3: `register_vec_primitives()` in `builtins.rs` registers 4 Vec primitives with polymorphic type schemes (`forall a. ...`). Used `fresh_var_id()` to allocate type var IDs, avoiding collision with `next_id=0` which caused infinite recursion in `apply`. 32 Vec integration tests + 4 REPL Vec tests now pass. 5 unit tests added. |

### U1.13 — REPL spec compliance: 6 Ring 0 requirements not met

| Field | Value |
|---|---|
| **ID** | U1.13 |
| **Source skill** | `/repl` |
| **Category** | `ergonomics` |
| **Severity** | `blocking` |
| **Description** | Sprint 4/5 compliance audit found 10 `repl/spec.md` Ring 0 requirements that the implementation does not meet: (1) §1.3: `(defn double [x] (* x 2))` shows `:(Fn [Int] Int) <closure>` — should show `:(Fn [Int] Int) user/double`. (2) §1.4: Types show bare `Int` not `primitives/Int`. (3) §1.5: ADT constructors show bare `Red` not `Color.Red`. (4) §2.1: Prompt is `> ` not `{compile}+{eval}ms; {module}>`. (5) §4.1: Bare function lookup shows `<closure>` not the function name. (6) §6.2: No startup banner (spec requires name, version, `/help` hint). (7) §3.1: Slash commands completely broken — `/help` parses `/` as division operator producing `error: undefined variable: /`. All Ring 0 slash commands (`/help`, `/sig`, `/doc`, `/type`, `/info`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/list`, `/time`, `/quit`) are non-functional. (8) §4.1: Bare type name lookup (`Int`) produces `error: undefined variable: Int` instead of type information. (9) §4.1: Bare trait name lookup (`Num`) produces `error: undefined variable: Num` instead of trait information. (10) §4.2: Bare special form lookup (`if`) produces an error instead of showing the form's shape. Items 7-10 completely block the §6.1 "first five minutes" discoverability journey — a new user cannot discover the language at all. |
| **Responsible skill** | `/qa` (implementation in `src/repl.rs`) |
| **Status** | `open` |
| **Resolution** | — |

---

## Ring 2: Abstraction

### U2.1 — Display trait not registered at startup, blocking stdlib bootstrap

| Field | Value |
|---|---|
| **ID** | U2.1 |
| **Source skill** | `/stdlib` |
| **Category** | `missing API` |
| **Severity** | `important` |
| **Description** | Ring 2A registers three core traits at startup (Num, Eq, Ord) per arch decision 17, but not Display. The stdlib bootstrap sequence requires Display for `testing/assertions.cl` — `assert-eq` needs to render expected vs actual values in failure messages using `show`. Without Display at startup, either: (a) Display must be declared in a stdlib module (requires the module system, Sprint 5), delaying the test bootstrap, or (b) `assert-eq` must use type-specific primitives (`int-to-string`, `float-to-string`, etc.) directly, losing generic rendering. Option (a) creates a circular dependency: assertions need Display, but Display's own tests need assertions. Option (b) is workable but limits `assert-eq` to a fixed set of types. **Recommendation**: Add Display to startup registration alongside Num/Eq/Ord. The four display primitives (`int-to-string`, `float-to-string`, `bool-to-string`, `string-identity`) already exist as Ring 1 externs, so the builtin impls can map directly to them. This is a planning-stage decision for Sprint 5. |
| **Responsible skill** | `/arch` (decision), `/typecheck` (implementation) |
| **Status** | `open` |
| **Resolution** | — |

---

## Ring 3: Meta

*No findings yet.*

---

## Ring 4: Effects

*No findings yet.*
