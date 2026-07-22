# Sprint 116 — single method-signature resolution

Owner: `/design` narrow-deployed to `cranelisp-typecheck`. This elaborates
`typecheck.md` and `traits.md` for `spec/07-traits.md` §7.1, §7.1.1, and
§7.1.5. The frontend owns structural parsing; typecheck owns the semantic
classification of the one method tail.

## 1. One tail, one classification

Every parsed method reaches typecheck with exactly one unresolved trailing
form and its span. Typecheck classifies it once, at trait-declaration
registration:

1. An `Sexp::Annotated` tail is unconditionally a value expression. Its
   annotation constrains the default body's inferred result; it is never
   offered to type resolution. This is the direct consequence of the reader
   folding `:Type subject` into one node.
2. Otherwise, run the ordinary trait-signature `TypeExpr` resolver in a
   **non-raising, transactional probe**. The probe uses the same module view,
   `self` binding, HKT constructor variables, and method-local type-variable
   rules as final signature resolution. It may return `Resolved(type_expr)` or
   `NotAType`; it must not publish minted variables, constraints, side-map
   entries, or diagnostics while probing.
3. `Resolved` classifies a required method. `NotAType` builds and retains the
   same form as the default body expression. Structural failure to build that
   expression is a located error at the tail; a later name/type failure is
   reported while instantiating the default for an impl.

This is one classifier, not `parse_type_expr` followed by recovery. In
particular, a name that resolves as both type and value takes the type reading;
an enum constructor or ordinary value name that does not resolve as a type is a
body. Unknown/malformed type-looking spelling does not leak an `invalid type
expression` error from the probe: it takes the expression branch and receives
the ordinary value/body diagnostic if that branch is invalid.

The deleted `[params] return-type body` spelling never reaches this classifier:
frontend rejects its second trailing element. Typecheck has no compatibility
arm for it and no legacy `ret_type + default_body` interpretation.

This follows **Resolve once**, **Single source of truth**, **No interim
implementations of later-ring capabilities**, and **Record from settled
state**: classification is produced once from the complete declaration scope
and every later registry/impl consumer reads the classified result.

## 2. Classified method representation

After classification, typecheck works with a closed semantic sum:

- `Required { ret_type }`
- `Default { body, result_constraint }`

`result_constraint` is absent for an inferred default and contains the ordinary
body annotation when one was written. There is no state in which a method is
simultaneously required and default, and no mandatory synthetic return type for
an unannotated default.

The unresolved cross-crate carrier and this classified sum require an
`/arch`-approved `cranelisp-types` change. The minimum contract is: preserve one
raw tail through the frontend/typecheck boundary, then store one classified
method kind in the symbol-table declaration. The old independent
`ret_type: TypeExpr` plus `default_body: Option<Expr>` fields cannot remain as a
second semantic authority. Exact Rust names belong to `/arch`; typecheck adds no
public function and changes none of `cranelisp-typecheck/public-api.txt`.

Because the carrier is serialized in `TraitDecl`/symbol tables, it rides the
same coordinated schema 22→23 window as `Sexp::Annotated`. It does not justify a
second schema bump. The `Sexp::Annotated` variant is consumed structurally at
the classifier boundary and becomes the existing expression-annotation
semantics; typecheck adds no annotation sidecar.

## 3. Occurrence and declaration registration

The implementing-type occurrence check remains conventional-trait-only and
declaration-time, before any registry write. It reads the classified method:

- required method: occurrence in any parameter or in `ret_type`;
- default method: occurrence in any parameter or in an explicit annotated-body
  result constraint; an unannotated body is not scanned for an occurrence.

The body is deliberately irrelevant: occurrence is a dispatch property of the
signature, and a body variable/reference does not create a dispatch position.
Thus a default with a bare parameter is accepted, a default with all parameters
annotated away from `self` and a concrete result constraint is rejected, and a
default whose body merely mentions a self-typed value is still rejected. A
default constrained as `:self body` supplies the return-position occurrence.
HKT declarations continue to return through their dedicated registration
branch before this conventional occurrence loop.

The rejection is located at the method tail/signature span and retains the
spec-pinned reason, `no occurrence of the implementing type`. It may explain
that a default needs a bare/`:self` parameter or a `:self` body constraint, but
there is one diagnostic site and one reason string.

## 4. Default inference and impl conformance

A default body is a per-impl template. For every impl that omits it:

1. Substitute the concrete implementing type into parameter annotations and
   method-local variables.
2. Bind exactly the declared parameter names.
3. Infer the body in the trait-definition module, against the impl's concrete
   `self` and sibling-method enrollment.
4. If `result_constraint` exists, unify the inferred result with it and locate
   a mismatch at the annotation/body tail.
5. Record the settled inferred function type on the generated method def only
   after inference completes.

An override never instantiates the default template. A provided impl method is
checked against the classified required/default declaration uniformly:

- written parameter count must equal the declared count before body checking;
- each provided parameter type must conform after `self` substitution;
- required methods conform to their declared return type;
- overrides of inferred defaults conform to the default method's parameter
  contract and any explicit result constraint, while their body result is
  otherwise inferred.

Too many and too few parameters are symmetric located conformance errors at the
impl method; an extra binder is never silently dropped. Wrong parameter type,
wrong constrained result type, missing required method, and extra method all
fail before a partial impl enrollment is published.

Re-impl is a complete replacement transaction. It rebuilds omitted defaults
against the new sibling-method set, then atomically replaces the old enrollment
and its generated defs. A default body's sibling reference resolves from this
new settled enrollment, never from an invalidated prior impl. First impl and
re-impl use the same conformance and default-generation functions; there is no
redefinition-only repair path. This applies **Record from settled state** and
**Enforce invariants structurally**.

## 5. Errors and polarity

| Condition | Phase and location | Polarity |
|---|---|---|
| Missing or multiple trailing forms | frontend, missing/offending tail | reject before typecheck |
| Bare tail resolves as a type | declaration classifier | required; no body fallback |
| Bare tail does not resolve as a type | declaration classifier | default; no probe error emitted |
| Annotated tail | declaration classifier | always default body |
| No implementing-type occurrence | registration, method signature/tail | reject before registry write |
| Default body cannot typecheck for an impl | per-impl instantiation, body expression | reject; name default method |
| Default result violates annotation | per-impl instantiation, annotation/body | reject with expected/actual |
| Impl arity/type mismatch | impl preflight, impl method | reject before enrollment/writeback |
| Deleted three-element spelling | frontend, second trailing element | reject; never reinterpret |

Probe failures are not swallowed errors: `NotAType` is an expected negative
answer from a side-effect-free recognizer. Once the default branch is selected,
ordinary expression resolution is raising and preserves its own precise error.

## 6. Unit scenarios — submodule × class

Per **Tests mirror module composition**, `/dev(typecheck)` keeps tests beside
the owning strategy rather than in a pooled regression file.

| Submodule | Complexity | Edge | Negative |
|---|---|---|---|
| `traits/type_resolve` | applied/function type tail; method-local vars; HKT constructor context | type/value collision chooses type; `Sexp::Annotated` bypasses probe; probe leaves no minted state | unknown type-looking form becomes body; malformed body reports after classification; no probe diagnostic leakage |
| `traits/registry` | mixed required/default declaration | required occurrence in param and return; default occurrence in bare/`:self` param and `:self` result constraint | required and default no-occurrence twins; default body mention alone does not count; conventional/HKT polarity |
| `traits/impl_check` | inferred default calling sibling; annotated default; explicit override | zero-arg grammar reaches occurrence rule; first impl and re-impl; omitted default regenerated | arity high/low; wrong param/result; missing/extra method; no partial enrollment |
| `traits/dispatch` | required plus inferred-default siblings | override wins; omission selects fresh default; return-dispatched required method | re-impl sibling reference never targets stale def; ambiguous return dispatch stays located |
| `program/register` | multi-method trait cluster | classification completes before table write | one bad method leaves no partial trait/method entries |

The unit matrix includes the FIXME-0826 default column without duplicating its
fixture: accepted default by argument occurrence, accepted constrained default
by return occurrence, and rejected all-annotated/concrete default. It also pins
FIXME 0833's `{arity high, arity low, wrong param, wrong return, missing,
extra} × {first impl, re-impl}` matrix and the typecheck half of FIXME 0832's
default-sibling re-impl behavior. E2e ownership, spelling, and run/REPL/link
mirrors remain `/testing`'s responsibility under the Sprint 116 QA plan.

## 7. Quality attributes and impact

- **Simplicity/maintainability:** one unresolved carrier, one classifier, one
  closed classified sum, one impl-conformance path. The mandatory legacy return
  slot and three-element compatibility path are removed.
- **Observability:** errors distinguish structural arity, no occurrence,
  default-template failure, and impl conformance, each at the writer's form.
- **Testability:** the transactional probe and classifier are pure enough for
  direct unit tests; registry-write absence is asserted on every negative.
- **Concurrency:** unchanged. Classification and impl registration remain in
  the synchronous cluster staging transaction; no shared mutable state is
  introduced.
- **Performance:** one bounded type-resolution probe per method declaration;
  no runtime work and no repeated classification per impl.
- **Public/schema:** no typecheck public API delta. One `/arch`-owned types
  carrier/classified-shape delta shares schema 23 and requires the types public
  baseline/rustdoc update; frontend and int consume that coordinated window.

## Next skills

- `/arch` — settle the exact unresolved/classified carrier names and approve the
  single schema-23/types-baseline delta.
- `/testing` — land the missing failing-not-ignored default, conformance, and
  re-impl cells with `// spec:` traces.
- `/dev` (typecheck) — implement the classifier, occurrence/default inference,
  and unified conformance paths with the unit matrix above.
- `/review` (typecheck) — reject retained legacy fields/paths, probe mutation,
  partial enrollment, and re-impl-only repairs.
- `/sprint` — sequence the coordinated frontend/types/typecheck carrier wave.
