# ADT marker binding — mechanism selection

**Status:** adopted and implemented. `arch` approved the selected mechanism
(§4) because it touches the crate's public surface; `CLAdtType` itself is
unchanged, `cranelisp-types` is untouched, and the host load path and artifact
grammar are unchanged.

Scope is exactly one question: how a platform DLL binds a Rust marker type to a
cranelisp fully-qualified type name. It reopens no settled platform
architecture.

---

## 1. The problem

A DLL marshals a heap ADT as `CLAdt<T>`, where `T` is a zero-sized marker whose
only content is one string — `CLAdtType::TYPE_NAME`, the key into the embedded
schema artifact. Entries in that artifact are keyed by the same fully-qualified
type-expression string.

So one name is written **twice, independently**: once by the compiler into the
generated artifact, once by hand into the marker. Before this mechanism, nothing
compared them until runtime. That is the whole of the defect surface.

### 1.1 Where `TYPE_NAME` is consulted — and where it is not

| Path | Consults `TYPE_NAME`? | Effect of a wrong name |
|---|---|---|
| `read_field` / `own_field` | yes — the field lookup keys the schema by it | panic on lookup miss |
| nested-ADT field witness | yes — compared against the declared field type | panic on witness mismatch |
| `read_tag` | **no** — fixed offset, no schema | none |
| `construct` | **no** — tag and fields come from the author | **none, ever** |
| `from_raw`, `Debug` | no / display only | none |

Two consequences follow, and neither is obvious:

1. **A marker used only for construction is never validated at all.** A wrong
   name on such a marker is undetectable at runtime by construction — "accept
   runtime failure" is not even an available position for it.
2. **The layout-hash gate does not cover this.** That gate proves the artifact
   matches the host's live tables; it says nothing about whether a hand-written
   marker string names an entry the artifact declares. The two gates compose and
   neither subsumes the other.

---

## 2. Why runtime detection is not the cheap option

The observable failure mode depends on which call shape dereferences the marker,
and the two shapes differ sharply.

| Call shape | Fault containment | Observed failure on a name mismatch |
|---|---|---|
| Blocking effect thunk | DLL-local panic catch, monomorphised into the DLL, returned as an `EffectOutcome` fault | a diagnosed dispatch fault carrying the message and the effect's name |
| **Poll-shape leaf** | **none** — there is no panic catch anywhere on this crate's poll path, and the host does not wrap the call | an unwind out of an `extern "C"` frame ⇒ **process abort, no attribution** |
| Construct-only marker | n/a | never detected |

This asymmetry is the load-bearing finding. On the one production multi-ADT
platform, most markers are dereferenced *on the poll path*, where a disagreement
aborts the process. "Accept runtime failure with clear diagnostics" would
therefore first require adding fault containment to the poll boundary, or a
non-panicking read API — strictly more work and more surface than making the name
agreement structural.

---

## 3. Alternatives rejected

**Keep explicit marker impls and compensate with tests and diagnostics.** The
compensation package, not the status quo, is the cost: a production-path negative
witness is only meaningful once the poll path can be observed at all (§2), so the
containment work comes first. Retained as the documented fallback only if the
const-scanner premise is ever falsified — not as a live alternative.

**A derive macro.** Reduces boilerplate but leaves agreement at runtime unless a
second source of the artifact path is introduced, which is a second,
non-compiler-tracked authority for the same fact. It also adds a proc-macro
dependency and a second public crate on the external-author facade.

**A standalone marker macro** taking the schema text as an argument, instead of a
key on `declare_platform!`. Smaller diff, but it re-asks "which schema text?" at
a second site and can be forgotten entirely — an author who writes the marker by
hand gets no check.

---

## 4. The selected mechanism

An optional `adts:` key on `declare_platform!`, accepted **only on the arm that
embeds a schema**. Supplying markers without a schema is a macro match failure:
a platform that marshals no ADTs structurally cannot declare markers.

Each entry names a marker and its fully-qualified key, and carries the author's
own documentation through to the emitted type — the attribute passthrough is
required rather than cosmetic, because production markers carry load-bearing
rustdoc and a mechanism that discarded it would not be adopted. Per entry the
macro emits the marker type, its `CLAdtType` impl, and a **const assertion** that
the key names an entry the embedded artifact declares, with a message naming the
marker, the key and both repair actions.

The predicate is a `const fn` living beside the existing const layout-hash
scanner — the two const byte-scanners the macro depends on belong together, and
neither is a method on the parsed `Schema`, which does not exist yet when they
run. It sees exactly the bytes the runtime parser will see, so there is no second
path to the artifact.

**Paren-depth tracking is what makes it exact.** A bare textual search would also
match a *field type* occurrence, which is a reference rather than a declaration.
The scan skips comments and compares the atom opening each top-level entry.

**Scope limit, stated deliberately: bare `module/Type` keys only.** An applied
instantiation key is a parenthesized form whose spelling depends on the
generator's whitespace, so a byte compare is the wrong instrument for it. No
production marker uses one. The arm rejects such a key with a message saying so,
and an author who needs one writes an explicit `impl CLAdtType`, which stays
legal.

### What the check proves, and what it does not

- **Proves:** every marker emitted through `adts:` names a type the embedded
  artifact declares, at build time, for every consuming path — *including
  construct-only markers, which runtime never checks*.
- **Does not prove** that the artifact is current. That is the layout-hash gate's
  job: `adts:` is name agreement at build time, the layout hash is layout
  agreement at load time.
- **Does not prove** that a field-name string passed to `read_field` exists.

### Compatibility

`CLAdtType` remains a public, hand-implementable trait with an unchanged
contract; `adts:` is additive sugar over what an author can still write by hand,
so no out-of-tree DLL breaks. Two in-tree sites keep the hand-written form and
that is correct: the ABI-refusal fixture hand-rolls its manifest and embeds no
schema, and the crate's own test fixtures install synthetic schemas per test
binary rather than embedding an artifact.

---

## 5. Residual: the field-name axis

The mechanism does not close it. `read_field` takes a runtime string and panics
on a schema miss, and that is accepted.

One adjacent repair landed with the mechanism rather than after it, because it is
the message an author reads while debugging exactly this class of mistake: when
the *type key* is absent from the schema entirely, the field lookup and the
constructor lookup both come back empty, and the diagnostic used to blame the
**field name**. It now probes the type key first and reports a type-key miss with
the known keys, distinctly from a field miss.

**Reconsideration triggers:**

- **The field-name axis** — a reported mismatch on a field string, or a platform
  exceeding roughly a dozen distinct field names.
- **Applied instantiation keys** — the first production marker that needs one.
- **The Option-1 fallback** — only if a paren-depth byte scan over the embedded
  artifact proves not to be const-evaluable and exact. Its full compensation
  package would then be owed, poll-boundary fault containment included.

Per-marker generated field accessors are deliberately not designed here;
complexity has a budget (Principle 6), and each of these is a separate trigger
away.

---

## 6. Quality attributes

| Attribute | Assessment |
|---|---|
| **Simplicity** | One `const fn` and one macro key; no crate, no dependency, no trait change — the same idiom the crate already uses for the layout hash. |
| **Maintainability** | Blast radius is the production markers plus the macro. `CLAdtType` stays hand-implementable, so nothing out of tree breaks. |
| **Observability** | A build error naming the marker and the key replaces a runtime panic — or, on the poll path, an unattributed abort. |
| **Testability** (Principle 5) | The predicate is a pure total function over `&str`, unit-testable to its boundary and negative cells with no host, no DLL and no schema install. |
| **Concurrency-safety** | Untouched: no change to the poll ABI, `HostCtx` or the reactor boundary. |
| **Performance** | Untouched; the check is const-evaluated at zero runtime cost. |

The check is an instrument, so it is held to the arming discipline the repository
requires: a deliberately misspelled key must fail the build with the intended
message, and the correct spelling must build. Both legs live with the predicate's
own tests.

---

## 7. Cross-references

- `crates/cranelisp-platform/src/adt.rs` — `CLAdtType`, `CLAdt`, field resolution
- `crates/cranelisp-platform/src/declare.rs` — `declare_platform!` and the const
  scanners; per-item truth is their rustdoc
- `crates/cranelisp-platform/src/schema.rs` — artifact grammar and parser
- `design/platform/platform.md` §6 — the two gates and how they compose
- `design/arch/platform-interface.md` §5.5 — the generated-schema design
- `design/arch/bounded-contexts.md` §5 — the platform bounded context
