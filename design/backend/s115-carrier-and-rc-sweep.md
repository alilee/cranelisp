# S115 backend record — carrier attribution, RC-sweep discriminators, R4 and R6 censuses

**Status:** retained evidence plus the current R4 census. Every fix this S115
design scheduled has landed, and each current rule has a canonical home named in
its section. This record keeps what source cannot re-derive:

- the carrier-state attribution that split the S115 GOT-slot pair;
- the measurements that located the RC-release sweep's faces;
- the R4 mangle-family census, which
  [safety invariants R4](../arch/safety-invariants.md) cites.

Test outcomes cited here come from the S122 full-suite run of 2026-09-21. They
were not re-run for this record. Source and tests cite §1.3, §2–§4 and §6 by
number, so keep that numbering.

## 1. Carrier-state attribution for the GOT-slot pair

Two partial applications failed at the same wrapper-emission terminal:
"fn-as-value wrapper … reached codegen with no GOT-slot carrier". Before choosing
where to fix them, S115 dumped the carrier that each one presented at that seam.
The dumps split the pair into two fixes, one on each side of the carrier
contract.

| Repro | Carrier at the seam | Verdict | Where the fix lives |
|---|---|---|---|
| 0705: auto-curry over a `let`-bound closure, `(let [g (fn [a b] 0)] ((g 1) 2))` | `ApplyRef::ViaCallee`; callee `VarRef::Local`; no target FQ | Producer correct; backend emission arm missing | §3 |
| `=` partially applied inside a generic, `(defn g [x] (= x))` monomorphised at `Int` | `ApplyRef::Dispatch(prelude/=)`, which names the trait-method declaration and has no slot | Producer wrong | §1.3 |

### 1.1 The discriminator

The terminal fires after the direct, constructor and inline arms miss. At that
point the carrier is either absent or names an entry without a GOT slot. A dump
at the seam tells the two apart. An absent carrier is correct only for a
scope-stack or computed callee. A present carrier that reaches the terminal is a
producer error.

### 1.2 The local-closure face (0705)

A `let`-bound closure is a `VarRef::Local` and has no slot. The producer
therefore records `ViaCallee` correctly. The backend lacked an arm for currying a
closure value (§3). The born-green control is
`tests/shadowing_scope_lookup.rs::local_closure_auto_curry_non_trait_control_resolves_to_local`.

### 1.3 The `=` face: the producer boundary

**Rule:** never transport a trait-method declaration FQ as a dispatch carrier. A
declaration FQ is a dispatch-table key, not a slotted callable. This is one
instance of the carrier value-source rule in
[backend keyed consumption §1.1](../arch/backend-keyed-consumer.md).

**Evidence that located the gap:**

- The direct concrete control `(defn h [] (= 3))` resolved to
  `primitives/eq-i64` and ran.
- Only the generic-to-instance path failed. There, the auto-curry's trait
  resolution ran in the template context while the operand was still a type
  variable. It found no impl. The transport branch then carried the callee's
  `VarRef::Global(prelude/=)` through as the carrier.

**Realization:** typecheck owns the fix. A pre-settlement drain holds such an
entry back, then retries it once from settled state at finalization. The typecheck
[dispatch settlement queues](../typecheck/checked-body-publication.md#76-kept-separate-with-triggers)
describe this mechanism. The pin is
`tests/fn_as_value_carrier_loss.rs::trait_operator_partial_app_impl_present_has_got_carrier`,
which passes.

## 2. RC-release sweep

S115 scheduled three leak faces as one backend sweep. The measurements below
used `CRANELISP_RC_STATS` at the S115 head and are reported as allocations to
deallocations.

### 2.1 Entry-`main` heap payload — not a backend defect

| Program | Allocations/deallocations |
|---|---|
| `(defn main [] (let [s "hi"] (Pure 9)))` | 2/2 |
| `(defn main [] (let [s "hi"] (Pure s)))` | 2/1 |
| `(defn main [] (Pure "hi"))` | 2/1 |

The heap-payload leak was identical with the ownership toggle on and off. S115
first blamed `protect_return_value` and proposed two backend mechanisms. FIXME
0745 falsified both:

- The leaked reference belonged to the program's result value.
- Int is the only type-aware owner of that value.
- S118 fixed the leak at the
  [program-result owner](../int/result-owner.md).
- The pin is
  `tests/adt_drop_glue_underkey.rs::entry_main_ioresult_heap_payload_toggle_off_leak_r2`.

The backend owns only the function-return protect licence, which is what source
cites this section for. A freshly constructed return needs no protect in any
function. A return that may alias an argument or a live binding keeps its
protect. The licence is `value_provenance(body) <= Fresh`, defined in
[non-concrete release contract §6.1](non-concrete-release-contract.md#61-the-lattice).

Do not reintroduce the other rejected mechanism: releasing the payload inside the
IO-tree teardown. REPL display dereferences that payload after the tree has been
consumed, so releasing it there creates a use-after-free.

### 2.2 ADT-wrapped superseded loop parameter (0720)

A tail loop superseding a `(deftype G2 (Gr [cells]))` parameter leaked two
objects per iteration: 403/2 at N=200 and 803/2 at N=400. The ownership toggle
did not change the result. The bare-vector twin balanced at 202/202. Replacing
the parameter with an unrelated fresh `Gr` leaked identically. That isolated the
tail-jump parameter flush, not the match that consumes the parameter.

The fix landed. The current rule is the single transfer/replacement predicate
and its exemptions in
[transitive drop glue §6](transitive-drop-glue.md#6-tco-replacementtransfer-predicate).
The pins are the three tests in `tests/adt_wrapped_supersede_leak_0720.rs`,
including the bare-vector control. All three pass.

### 2.3 Acceptance bar

Each face must balance exactly (`allocs == deallocs`) under both toggles. Equal
imbalance between the toggles is not acceptance. That differential check cannot
see a leak that both lowerings share, and every leak found in S115 W3b was of
that kind (FIXME 0761). The standing exact-balance lane is QA's
`tests/gen_ownership_flows.rs`.

## 3. Auto-curry emission is total over the closed carrier sums

**Invariant:** every legal `(ApplyRef, VarRef)` state at the auto-curry seam has
an emission arm. The one illegal state is a located producer error. There is no
`_ =>` fallback and no re-resolution by name. The classifier is
`classify_auto_curry_target` in `crates/cranelisp-backend/src/compiler/apply.rs`.
Its closed result enum is the totality claim, and
`crates/cranelisp-backend/src/compiler/apply/auto_curry_totality_tests.rs` pins it.

| Carrier state | Emission arm |
|---|---|
| `Dispatch(fq)` naming a slotted callable | GOT-indirect wrapper call |
| `Dispatch(fq)` naming a function in the current unit | direct wrapper call |
| `Dispatch(fq)` naming a constructor or an inline primitive | constructor or inline-emission arm |
| `ViaCallee` with an inner trait-method or builtin resolution | impl carrier derived from that resolution |
| `ViaCallee` with a `VarRef::Local` or computed callee | curry the closure value (0705) |
| `ViaCallee` with a `VarRef::Global` callee and no inner resolution | located producer-contradiction error |

The last row is illegal because the producer transports a global plain-function
callee as `Dispatch`. The closure-value arm captures the closure alongside the
applied arguments and forwards through the closure call. It is the
partial-application counterpart of the locals-first rule for full application.

## 4. R4 — mangle-family injectivity census (owed O3; deliverable 4)

The rule comes from [safety invariants R4](../arch/safety-invariants.md): every
mangle from semantic identity to symbol must be injective, or keyed by an
additional disambiguator. This census was re-verified against source on
2026-09-24.

| Family | Mint | Key | Verdict |
|---|---|---|---|
| Type drop glue | `cranelisp_types::drop_glue_symbol_name` | Module plus full concrete instantiation | Witnessed at the types home. The backend-local escape scheme was deleted in S118. |
| GOT data symbol | `cranelisp_types::got_data_symbol_name`; the backend function forwards to it | Escaped module path | Witnessed since S119 (FIXME 0748). `crates/cranelisp-backend/src/compiler/resolution/tests.rs::got_data_symbol_name_agrees_with_the_types_owned_home` fences agreement with the backend forward. |
| Span-derived inner names: lambda bodies, closure and curry glue, fn-as-value, trait-method-value, operator and curry wrappers, parallel and launch continuations, dependent thunks and their glue, poll-state glue | `inner_fn_discriminator()` plus the span, composed at each site. Glue names go through `closure_drop_glue_name` and `curry_drop_glue_name`. | Injectively escaped enclosing instance name, then the gate-arm token, then the span's start and end | Across different spans: disambiguator-keyed; every composition site folds the span. Across instances of one template: the collapsed-character case is reproduced and corrected in S122; see the evidence and limits below. |
| Platform exports | `cranelisp-platform` `declare.rs`, via `concat!` | Platform name, verbatim | Keyed by platform-name uniqueness. The residual and its loader-side close are recorded in the R4 row. |
| Typecheck signature and method mangles | Typecheck's `$`/`+` joins | Joined FQ components | Stands with its rationale and is fenced; the R4 row carries both. |

The S122 cross-instance falsifier reproduced a duplicate lambda definition for
valid type names `A-B` and `A_B`; the `A-B`/`A-C` control passed. The discriminator
now escapes each non-alphanumeric UTF-8 byte, including underscore, as `_hh`.
The unit guard checks collapsed-character and escape-like spellings; the e2e
guard `tests/inner_fn_sanitized_name_collision.rs` passes fresh/cached REPL,
run and linked execution after failing in all six before the fix.
[QA's C-B closure](../../tests/plan/s122-evidence-delta.md) owns the exact evidence
and limits. This proves the discriminator correction, not every composed name:
the separate target component of curry wrapper names has not been re-examined.

## 5. R6 — persisted-index validation seam

The persisted-index census, the single validation loop and the maintenance rule
live in two places:

- the module rustdoc of `crates/cranelisp-backend/src/cache/serialize.rs`;
- [safety invariants R6](../arch/safety-invariants.md).

Every family is diagnosed as its own `CacheStale` class and triggers a
recompile. No arm uses `assert!`.

The borrowed-sibling slot is range-checked for `RustPrimitive` extern shims,
which are the only origin the lifecycle rules admit for that realization. The
slot still has no production reader. Out-of-range sibling slots are therefore
harmless today. That claim is asserted, with a falsifier: any production read of
`borrowed_sibling`. The first reader must also confirm that a restored extern
shim under any other origin is rejected. The range check depends on the origin
rule, and this seam propagates only the instance-key lifecycle error.

## 6. W-B5 patch-collapse — retired

The planned collapse of the three fn-return finders (`return_var_in_scope`,
`return_cow_source_in_scope`, `operand_live_binding_root`) onto one contract is
retired: they answer three different questions — exact same-frame cleanup slot,
carrier-keyed current-frame COW source, and name-valued provenance through
binding indirection — and their separation is the current design
([s122-closure.md](s122-closure.md) §5.1). Widening the fn-return skip to the
binding-indirection class remains a potential extension with a stated hazard and
trigger ([non-concrete-release-contract.md](non-concrete-release-contract.md)
§10).
