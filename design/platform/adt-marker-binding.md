# ADT marker binding — mechanism selection

**Status:** DESIGN, Sprint 118 Phase 3 (`/design` narrow-deployed to
`cranelisp-platform`). Design-only; no implementation this sprint.
**Selection is PROVISIONAL** — the recommended mechanism touches the crate's
public surface, so per S118 arch ruling 5 it **returns to `/arch` before
selection is final** (§10).

Answers FIXME 0873 / `audits/cranelisp-platform-s117.md` §R4 ("decide marker
binding ergonomics now that the deferred trigger has fired"). Scope is exactly
that question: how a platform DLL binds a Rust marker type to a cranelisp FQ
type name. It is not a canon rewrite of `design/platform/platform.md` (that is
FIXME 0871 / R2, S119) and it reopens no settled platform architecture.

---

## 1. The current contract

A platform DLL marshals a heap ADT as `CLAdt<T>`, a `#[repr(transparent)]`
wrapper over the allocation base pointer. `T` is a zero-sized marker whose only
content is one string:

```rust
pub struct Rectangle;
impl CLAdtType for Rectangle {
    const TYPE_NAME: &'static str = "shapes/Rectangle";
}
```

`TYPE_NAME` is the **key into the embedded schema artifact** — the
`/platform-schema`-generated text the DLL embeds via
`declare_platform! { schema: include_str!("<name>.platform-schema"), … }`, parsed
once at load into the process-global `Schema` (`adt.rs:90`,
`declare.rs:362-368`). Entries in that artifact are keyed by the same FQ
type-expression string:

```text
;; layout-hash: 3582bc7f3ed7f6f4
(schema
  (web/Connection
    (Connection 0 ((fd primitives/Int))))
  …)
```

So one FQ name is written **twice, independently**: once by the compiler into
the artifact, once by hand into the marker. Nothing compares them before
runtime. That is the whole of the defect surface this document addresses.

### 1.1 Where `TYPE_NAME` is consulted — and where it is not

| Path | Consults `TYPE_NAME`? | Effect of a wrong name |
|---|---|---|
| `CLAdt::read_field` / `own_field` (`adt.rs:185,202`) | yes — `resolve_field::<T>` keys the schema by it | panic on lookup miss |
| nested-ADT field witness (`ExpectedFieldType::Adt`, `adt.rs:321-328`) | yes — compared against the declared field type | panic on witness mismatch |
| `CLAdt::read_tag` (`adt.rs:172`) | **no** — fixed offset, no schema | none; silently fine |
| `CLAdt::construct` (`adt.rs:216`) | **no** — tag + fields come from the author | **none, ever** |
| `CLAdt::from_raw`, `Debug` | no / display only | none |

Two consequences the audit's framing did not separate:

1. A marker used **only** for construction is never validated at all. A wrong
   name on such a marker is undetectable at runtime by construction — "accept
   runtime failure" is not even an available position for it.
2. The layout-hash gate does **not** cover this. It proves the artifact matches
   the host's live tables (staleness); it says nothing about whether the DLL's
   hand-written marker string names an entry that exists.

---

## 2. The risk, characterized by call path

The mismatch's *observable* failure mode depends on which call shape
dereferences the marker, and the two shapes differ sharply.

| Call shape | Fault containment | Observed failure on a name mismatch |
|---|---|---|
| Blocking effect (`CLIO::effect*` thunk) | DLL-local `catch_unwind` inside the thunk (`lib.rs:975-1000`) — monomorphised into the DLL, so it is caught by the DLL's own panic runtime and returned as an `EffectOutcome` fault | diagnosed `DispatchFault` carrying the panic message + the effect's fn name |
| Poll-shape leaf (`PollFn` = `unsafe extern "C" fn(state, *HostCtx, *Waker) -> Poll`) | **none** — there is no `catch_unwind` anywhere in `cranelisp-platform`'s poll path, and the host does not wrap the call | unwind out of an `extern "C"` frame ⇒ **process abort**, no attribution |
| Construct-only marker | n/a | never detected |

This is the load-bearing finding of the comparison. On the one production
multi-ADT platform, three of the four markers are dereferenced **on the poll
path**:

- `exemplar/platforms/web/src/lib.rs:376-377` — `CLAdt::<Listener>::from_raw(env.arg(0)).read_field("fd")` in `accept_conn_pollfn`
- `:439-440` — the same shape for `Connection` in `read_conn_pollfn`
- `:611-614` — `Response`'s three field reads in `ensure_write_buffered`, called from the send leaf

A marker/schema name disagreement on any of those aborts the process. "Accept
runtime failure with clear diagnostics" therefore is **not currently on the
table as a cheap option**: on the production path that the trigger fired for, it
would first require adding fault containment to the poll boundary (or a
non-panicking read API), which is strictly more work and more surface than
making the name agreement structural.

---

## 3. Binding census (2026-07-25)

| Site | Markers | Read path | Notes |
|---|---|---|---|
| `exemplar/platforms/web/src/lib.rs:85-115` | 4 (`Listener`, `Connection`, `Request`, `Response`) | poll leaves (3) + construct-only (`Request`) | the S87 deferral trigger; each marker carries substantial rustdoc |
| `platforms/shapes/src/lib.rs:39-45` | 1 (`Rectangle`) | blocking effect thunk | the reference ADT platform |
| `platforms/shapes-badabi/src/lib.rs:64-67` | 1 (`Rectangle`) | never dispatched | hand-rolled manifest, **no `schema:` arm**; a deliberately-broken ABI-gate fixture |
| `crates/cranelisp-platform/tests/*.rs`, `src/adt/tests.rs` | 8 across 5 files | test fixtures | synthetic schemas, per-binary `GLOBAL_SCHEMA` isolation (FIXME 0874's subject) |

Five production markers, four of them added in one platform. The S87
deferral condition ("wait for a real multi-ADT platform") is satisfied.

---

## 4. Option comparison

### Option 1 — keep explicit marker impls

Change nothing; compensate with a production-path negative witness plus
diagnostics quality (the audit's stated bar).

- **Cost to build:** the compensations, not the status quo — a negative witness
  that a wrong `TYPE_NAME` fails the way we claim it does, on a production call
  shape. Per §2 that witness would have to be written against the poll path,
  where today the honest expected outcome is *process abort*. Making it a
  legible diagnosed failure means adding poll-boundary fault containment.
- **What it cures:** nothing structurally. The two independent copies of the FQ
  name remain, and the construct-only marker stays permanently unverifiable.
- **Verdict:** the compensation package is larger than the cure in Option 3,
  and it still leaves the mismatch class live. The audit explicitly rules out
  the cheap version ("merely adding another positive test does not cure the
  mismatch risk"). Not recommended — retained as the fallback if `/arch`
  rejects Option 3 (§11).

### Option 2 — a derive macro

`#[derive(CLAdtType)] #[cladt(name = "shapes/Rectangle")] pub struct Rectangle;`

- **Cost:** a new proc-macro crate (`cranelisp-platform-derive`) with
  `syn`/`quote`/`proc-macro2` in its tree. Every out-of-tree DLL author gains
  that build dependency and its compile time. `cranelisp-platform` is the
  **external-audience facade** (Principle 15) and today its dependency story is
  "one crate, no `libloading`, no frontend" — a proc-macro crate is a visible
  regression of that story. It is also a second permanent public surface with
  its own versioning obligations.
- **What it cures:** the boilerplate (`struct` + `impl` + `const` → one
  attribute). It does **not** cure the mismatch: a derive expands with no
  access to the `include_str!`'d artifact. To check the name it would have to do
  its own file IO at expansion time, re-deriving the artifact path from
  `CARGO_MANIFEST_DIR` — a second, non-compiler-tracked source of truth for
  where the schema lives (violates Principle 7, and loses `include_str!`'s
  rebuild-on-change dependency tracking).
- **Verdict:** highest cost, strictly weaker guarantee than Option 3. Rejected.

### Option 3 — macro-emitted binding, checked against the embedded schema

Extend `declare_platform!` with an optional `adts:` key that emits each marker
**and** a compile-time assertion that its name is an entry in the artifact the
same macro invocation embeds.

- **Cost:** one `const fn` predicate in `declare.rs` beside the existing
  `extract_layout_hash` (the same idiom — a const byte-scanner over the artifact
  text), one optional macro arm, and migration of the five production markers.
  No new crate, no new dependency, no `CLAdtType` contract change.
- **What it cures:** name agreement becomes a **build error**, not a runtime
  event — including for construct-only markers that runtime never checks
  (Principle 18, enforce invariants structurally). The two copies of the FQ name
  remain textually, but they are now compared by the compiler at the point
  where both are in scope (Principle 7's spirit: one authority, mechanically
  enforced agreement).
- **Verdict:** smallest shape that makes agreement structural. **Recommended.**

### Decision table

| | Boilerplate | Name agreement | New dependency | New public surface | Covers construct-only |
|---|---|---|---|---|---|
| 1 — explicit impls | unchanged | runtime, path-dependent (abort on poll path) | none | none | no |
| 2 — derive | reduced | still runtime (unless a second schema-path source is introduced) | proc-macro crate for every DLL author | derive crate | no |
| 3 — macro + const check | reduced | **compile time** | none | one `const fn` + one macro key | **yes** |

---

## 5. The selected shape (pinned)

### 5.1 Macro surface

A new optional `adts:` key, accepted **only on the `schema:` arm** of
`declare_platform!` (arm 1). Omitting `schema:` and supplying `adts:` is a macro
match failure — a platform that marshals no ADTs structurally cannot declare
markers.

```rust
declare_platform! {
    name: "web",
    version: "0.1.0",
    host: HOST,
    schema: include_str!("web.platform-schema"),
    adts: [
        /// Marker for the `web/Listener` ADT (the value `bind-listener` constructs).
        Listener   => "web/Listener",
        /// Marker for the `web/Connection` ADT — an OPAQUE handle carrying `fd`.
        Connection => "web/Connection",
        Request    => "web/Request",
        Response   => "web/Response",
    ],
    functions: [ … ]
}
```

Per entry the fragment is `$(#[$attr:meta])* $marker:ident => $key:literal` —
the attribute repetition is required, not cosmetic: the four web markers carry
load-bearing rustdoc today (`lib.rs:85-115`) and a mechanism that silently
discards it would not be adopted. Expansion per entry:

```rust
$(#[$attr])*
pub struct $marker;

impl $crate::CLAdtType for $marker {
    const TYPE_NAME: &'static str = $key;
}

const _: () = assert!(
    $crate::schema_declares_type(__CRANELISP_PLATFORM_SCHEMA_TEXT, $key),
    concat!(
        "declare_platform!: ADT marker `", stringify!($marker), "` names \"", $key,
        "\", which is no entry in this platform's embedded schema. Check the ",
        "fully-qualified spelling (module/Type), or regenerate the artifact with ",
        "`/platform-schema <name>` if the type was added or renamed."
    ),
);
```

`__CRANELISP_PLATFORM_SCHEMA_TEXT` is already emitted by arm 1
(`declare.rs:219`), so the check sees exactly the bytes the runtime parser will
see — no second path to the artifact. `assert!` with a `concat!`-built literal
message is const-evaluable; the message names the marker, the key, and both
repair actions.

### 5.2 The predicate

```rust
pub const fn schema_declares_type(artifact: &str, type_key: &str) -> bool
```

Home: `declare.rs`, beside `extract_layout_hash` — the two const byte-scanners
the macro depends on belong together, and neither is a `Schema` method (`Schema`
is the runtime parsed form; these run before it exists).

Algorithm: scan bytes tracking paren depth, skipping `;;` comments to end of
line. Entries live at depth 1 inside `(schema …)`; at each `(` that opens depth
2, compare the following atom against `type_key` byte-for-byte, terminated by
whitespace or `(` or `)`. Return `true` on the first match. Depth tracking is
what makes it exact — a bare textual `strstr` would also match a *field type*
occurrence such as `(inner (primitives/IO _))`, which is a reference, not a
declaration.

Scope limit, stated deliberately: **bare FQ keys only** (`module/Type`). An
applied instantiation key (`(primitives/IO primitives/Int)`) is a parenthesized
form whose textual spelling depends on the generator's spacing, so a raw byte
compare is not the right instrument for it. No production marker uses an applied
key today. If one ever does, the author writes an explicit `impl CLAdtType`
(which stays legal — §5.4) and the `adts:` arm rejects a key containing `(` or
whitespace with a `concat!` message saying so.

### 5.3 What the check proves, and what it does not

- **Proves:** every marker emitted through `adts:` names a type the embedded
  artifact declares, at build time, for every consuming path including
  `construct`.
- **Does not prove:** that the artifact is current. That remains the layout-hash
  gate's job (host regenerates from live tables, compares against
  `__cranelisp_layout_hash_<name>`; `--run`/`--link` refuse, REPL warns). The two
  gates compose cleanly and neither subsumes the other: **`adts:` = name
  agreement at build time; layout hash = layout agreement at load time.**
- **Does not prove:** that a `read_field("…")` field-name string exists. Field
  names remain runtime strings (§6).

### 5.4 Compatibility and exceptions

`CLAdtType` stays a public, hand-implementable trait with an unchanged contract;
`adts:` is purely additive sugar over what an author can still write by hand.
Two current sites keep the hand-written form and that is correct:

- `platforms/shapes-badabi` — hand-rolls its manifest to bake a stale
  `abi_version`, so it never invokes `declare_platform!` and embeds no schema.
  Its marker is never dispatched (the host refuses the DLL at load).
- The crate's own test fixtures — they install synthetic schemas per test binary
  rather than embedding an artifact.

Migration is therefore three in-tree markers-with-schema call sites (web ×4,
shapes ×1), each a mechanical move of the existing `struct` + `impl` + rustdoc
into the new arm.

### 5.5 Rejected sub-variant

A standalone `platform_adts!(SCHEMA_TEXT, [ … ])` macro instead of a
`declare_platform!` key: smaller diff, but it re-asks "which schema text?" at a
second site and can be forgotten entirely — an author who writes the marker by
hand gets no check. Folding the emission and the check into the one macro every
DLL already invokes exactly once makes the check unforgettable (Principle 18).

---

## 6. Residual runtime-failure surface (accepted)

The selected mechanism does not close the field-name axis: `read_field("fd")`
takes a runtime `&str` and panics on a schema miss. That residual is accepted
for now, and it carries one obligation that lands **with** the implementation,
not after it:

**`resolve_field`'s miss diagnostic misattributes a type-key miss as a field
miss.** When `T::TYPE_NAME` is absent from the schema entirely, `field_offset`
and `ctor_names` both return `None`, so the panic at `adt.rs:359-370` prints
`constructors:[]` and blames the *field name* — the one message an author would
read while debugging exactly the mismatch this document is about. The fix is
crate-internal and small: probe `schema.lookup_type(type_key)` first and emit a
distinct "type key not in this platform's embedded schema; known keys: […]"
message. This is worth doing regardless of which option `/arch` selects, and it
is the diagnostics half of Option 1's compensation package if Option 3 is
rejected.

Future extensions deliberately **not** designed here (Principle 6 — complexity
has a budget): compile-time field-name checking, per-marker generated field
accessors, applied-key marker support. Each is a separate trigger away.

---

## 7. Quality attributes

- **Simplicity** — one `const fn` and one macro arm; no crate, no dependency,
  no trait change. The mechanism is the same idiom the crate already uses for
  the layout hash.
- **Maintainability** — blast radius is the five production markers plus the
  macro. `CLAdtType` remains hand-implementable, so no out-of-tree DLL breaks.
- **Observability** — a build error naming the marker and the key replaces a
  runtime panic (or, on the poll path, an unattributed abort). The §6
  diagnostic repair covers the residual runtime path.
- **Testability** (Principle 5) — the predicate is a pure total function over a
  `&str`, unit-testable to the boundary/negative cells directly, in the idiom of
  `declare.rs`'s existing `extract_layout_hash` scanner tests.
- **Concurrency-safety** — untouched. This sprint's platform slice makes no
  change to the poll ABI, `HostCtx`, or the reactor boundary.
- **Performance** — untouched; the check is const-evaluated, zero runtime cost.

---

## 8. Verification ideas (future rows, not S118 obligations)

Per `tests/plan/s118-test-plan.md` §7, 0873 is design-only and carries no test
cells this sprint. When the mechanism is implemented, the cells the design
implies are:

1. `schema_declares_type` unit cells in `declare.rs`'s existing test module:
   present-entry, absent-entry, present-only-as-a-field-type (the depth-tracking
   negative), comment-embedded near-miss, empty artifact, applied-form key
   rejection.
2. A compile-fail cell (`trybuild`-style or a documented manual check) that a
   misspelled `adts:` key fails the build with the intended message — the
   negative witness the audit asked for, relocated from runtime to build time,
   where it is deterministic.
3. The §6 diagnostic: a unit cell pinning that a read against an unknown type
   key reports the *type* miss, not a field miss.

`/qa` owns whether these become plan rows; they are recorded here as the
design's implications, not as obligations levied on this sprint.

---

## 9. `/arch` return gate (S118 ruling 5)

The recommendation **touches `cranelisp-platform`'s public surface**, so per
arch ruling 5 the selection is **not final** until `/arch` reviews. The exact
delta to approve:

| Item | Kind | `public-api.txt` impact |
|---|---|---|
| `pub const fn schema_declares_type(&str, &str) -> bool` | new public fn | one added line (additive) |
| `adts:` key on `declare_platform!` arm 1 | new external-author macro contract | none (macros are not in the baseline) — but it is external-audience surface under Principle 15 |
| `CLAdtType` trait | **unchanged** | none |
| `CLAdt` / `CLTypeWitness` / `Schema` | **unchanged** | none |

No cross-crate interface is involved: `cranelisp-types` is untouched, no cache
schema version moves, the backend generator and the artifact grammar are
unchanged, and the host load path is unchanged.

## 10. Reconsideration trigger

- **If `/arch` approves:** implementation is a follow-on `/dev`(platform) wave
  (S119 or later), landing the predicate, the arm, the five call-site
  migrations, and the §6 diagnostic in one change-set.
- **If `/arch` rejects Option 3:** the fallback is Option 1 with its full
  compensation package — the §6 diagnostic repair **plus** poll-boundary fault
  containment (so the production-path failure is diagnosable rather than an
  abort) **plus** the negative witness against that contained path. The
  rationale for staying with explicit impls must be recorded here, and the
  reconsideration trigger becomes: *any* new platform that marshals an ADT on a
  poll leaf, or the first field-name-axis mismatch reaching a user.
- **Independent of the choice**, the trigger for revisiting the field-name axis
  is a reported mismatch on a field string, or a platform exceeding roughly a
  dozen distinct `read_field` names.

## 11. Cross-references

- `crates/cranelisp-platform/src/adt.rs` — `CLAdtType`, `CLAdt`, `resolve_field`
- `crates/cranelisp-platform/src/declare.rs` — `declare_platform!`,
  `extract_layout_hash` (the const-scanner idiom this design extends)
- `crates/cranelisp-platform/src/schema.rs` — artifact grammar + parser
- `design/arch/platform-interface.md` §5.5 — the generated-schema design
- `design/arch/bounded-contexts.md` §5 — platform bounded context
- `audits/cranelisp-platform-s117.md` §2.2, §R4 — the finding this answers
