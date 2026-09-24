# Constructor keys

Current architecture contract owned by `arch`: the one storage-key grammar for
constructors and the obligations it places on every writer and reader across
types, typecheck, backend and the binary. Exact signatures live in source
rustdoc. Member storage in general is
[the symbol-table lifecycle](symbol-table-lifecycle.md#58-constructors-and-accessors);
the resolved-identity carrier contract that generalises §10 is
[backend keyed consumption](backend-keyed-consumer.md); typecheck's
registration interior is [dotted constructor registration](../typecheck/dotted-ctor-registration.md).
Language authority is [the module specification](../../spec/08-modules.md) §8.5
and §8.6.5 and [pattern matching](../../spec/06-pattern-matching.md) §6.2.1.
The S109 coordinated landing, its measured regression classes and its commit
structure are delivery history in Git. Section numbers are stable citation
targets from source and tests; the gaps are intentional.

## 1. The uniform keying rule (all writers)

- A **sum or enum constructor**'s binding is stored under the canonical
  `member_key(Type, Ctor)` key (`Maybe.Some`) in the type's home module. The
  bare constructor name is a `NameCandidate` exposure onto that key, not a
  second binding. Two types exposing one bare constructor name produce two
  candidates for that spelling; selection is use-site.
- A **product constructor** shares its type's name and keeps the single
  type-name key. It has no dotted key and no bare exposure.
- Every writer applies the rule through the shared types ADT builder: user
  `deftype` registration in typecheck, typecheck's fixture seeds, and the
  binary's bootstrap seeds (`register_synth_adt` and the hand-appended `IO.Bind`
  in [bootstrap](../../src/bootstrap.rs)). No writer may store a sum
  constructor under its bare name.

The bare-key fallback that readers keep (§3) serves the product facet only. It
does not license a third keying.

## 2. Storage keys at the types reader and in the cache

- `cranelisp_types::type_ctor_names` returns **storage keys**: the canonical
  member key for each sum constructor and the type-name key for the product
  facet. It is the one mapping from a type's declared constructor names to
  keys; layout and heap-classification consumers delegate to it rather than
  rebuild the rule.
- Key meaning is serialized in `.meta.json`. A change to the key grammar is a
  cache key-meaning change and bumps `CACHE_SCHEMA_VERSION` in the same
  change-set as the writers. A dotted-constructor program must resolve
  identically cold and warm.

## 3. Reader obligations

Any reader that finds a constructor from a type and a bare constructor name
probes the canonical member key first and the bare key second. Current
readers, each carrying its own rustdoc:

1. Backend `CompileContext::constructor_metas` and the schema constructor
   projection.
2. The binary's value display, `ctor_field_types`.
3. The binary's member-glob import, `collect_member_glob`, which also exposes
   the bare spelling for each canonical member it imports, mirroring the home
   module's exposure.
4. Typecheck exhaustiveness and constructor instantiation.
5. Same-module member resolution during a cluster. A bare member spelling whose
   candidate names the current module is read through the caller's first-hop
   view, staging over live, not from the committed table alone. This is a
   property of the types resolver
   ([the one lookup](prelude-import-convergence.md#31-shape-and-home)), so
   typecheck carries no staging-specific fallback of its own.
6. REPL introspection, `/list`, `/search` and session save read constructor
   metadata from terminal bindings under their canonical member keys, never
   from a bare spelling. A constructor is listed once, under its canonical form
   ([agent language awareness](../../repl/spec/17a-agent-language-awareness.md) §17.19.2b).
   A bare constructor or accessor spelling exposed by several types is an
   ordinary several-candidate spelling: introspection reports each canonical
   member ([REPL introspection](prelude-import-convergence.md#35-repl-introspection)).

## 6. Accessors share the mechanism

A bare field-accessor name is exposed onto its canonical `Type.field` key by
the same candidate mechanism, so §3 reader 5 governs it identically. A bare
accessor that failed to resolve within its own cluster under `--run` was the
defect that motivated that rule.

## 7. Pattern position is scrutinee-directed

Spec §6.2.1 and §8.6.5 rule 4 govern. A bare constructor pattern whose spelling
has several candidates is selected by the scrutinee's type at the pattern's
check point. The answer depends only on that type: no fixpoint, no arm-order
sensitivity. A dotted pattern head always selects directly. Value position
uses ordinary typed selection under §8.6.5.

## 10. The resolved pattern constructor reaches codegen

Typecheck resolves a pattern constructor once; the backend reads that answer
and never resolves the source-written name again. Re-encoding the identity as
text for the backend to parse was rejected: a missed rewrite would silently
fall back to context-free resolution.

### 10.1 `pattern_ctors` carries the storage identity

`MethodResolutions.pattern_ctors` maps a constructor pattern's own span to the
`FQSymbol` under which the constructor's binding resolved: the canonical member
key for a sum constructor, the type-name key for the product facet. It is not
the display name. Constructor instantiation is the single mint point.

### 10.2 Transport on the mono node

`MonoMatchArm.resolved_ctor` is `Some` for constructor-pattern arms and `None`
for wildcard and variable arms. `MonoExpr::from_expr` and
`MonoExpr::lenient_from_expr` take the `pattern_ctors` map as a required
parameter, so a codegen view cannot be built without answering the question
([Principle 18](principles/18-enforce-invariants-structurally.md)). Typecheck is the
sole producer of mono views; synthesized bodies, whose nodes have no source
span, populate the field directly at synthesis. The field serializes with the
codegen view, so a change to its population is a cache schema change.

### 10.3 Consumption: read, never resolve

`compile_constructor_pattern` takes the arm's `resolved_ctor` and performs the
direct keyed read `CompileContext::ctor_meta_at`: no name resolution, no
fallback and no map-iteration order. A `None` carrier or a key that fetches no
constructor is a hard `CodegenError`. The backend has no name-based constructor
resolver in any position; value-position consumers use the keyed carriers of
[backend keyed consumption](backend-keyed-consumer.md).

### 10.4 Sparkability's constructor-exclusion set

Spark admission excludes constructor calls. The exclusion set holds storage
keys while call sites hold source spellings, so both sides pass through
`cranelisp_types::bare_member_name` before comparison. Terminal-segment
granularity is acceptable because the surface is a heuristic, not a
correctness rule.

### 10.5 Keying drift fails loudly in debug builds

`constructor_metas` and the schema constructor projection `debug_assert!` when
a declared constructor's canonical and bare probes both miss. Release builds
skip the constructor. Without the assertion, keying drift would surface as a
wrong heap classification or schema, not as an error.

### 10.6 Depth guard

`CHAIN_FOLLOW_DEPTH_LIMIT` bounds the scoped module-alias walk; its pin is
`alias_walk_refuses_more_than_the_shared_depth_limit` in
[the resolver tests](../../crates/cranelisp-types/src/resolve/tests.rs).
Candidate resolution itself follows no chain and needs no bound.
