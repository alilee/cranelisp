# S122 typed consume closure — intrinsics

Owner: `/design` (intrinsics). Status: **Intrinsics producer, internal callers,
primitives/backend consumers and exact-site guard delivered; Binary/int,
integrated evidence and generated baseline pending**.
Compiler checkpoint: `dc78ddbe`. This is the current entry point for the
intrinsics half of the approved typed consume migration, ACT-0956, and Q3's
continuation-produced `Bind` ownership correction. The
cross-pair contract remains
[`s119-typed-consume-funnel.md`](../runtime/s119-typed-consume-funnel.md); the
bounded context and approved Rust surface are in
[`bounded-contexts.md` §4b](../arch/bounded-contexts.md#4b-intrinsics--cratescranelisp-intrinsics).

The target is already approved. On 2026-09-10 the user also approved D8's
bounded private primitives construction/traversal/storage amendment. It adds
no handle operation, signature, visibility, consumer edge, emitted-call ABI,
heap layout, catalog entry, schema or technology choice.

## 1. Delivered intrinsics source and pending baseline

Current source now contains `crates/cranelisp-intrinsics/src/handle.rs`; all nine
consuming functions and `consume_vec_with`'s callback use the approved typed
surface below, and their named same-crate production callers are adapted. The
committed `crates/cranelisp-intrinsics/public-api.txt` still records the old raw
`i64` surface. It is a pending generated artifact, not evidence that the producer
source remains unimplemented. The delivered source surface is:

| Function | Target parameter types |
|---|---|
| `rc::consume_shallow` | `Owned` |
| `drop::consume_slist`, `drop::consume_sexp` | `Owned` |
| `drop::consume_vec_with` | `Owned, fn(Owned)` |
| `drop::consume_vec_of_string`, `drop::consume_io_tree` | `Owned` |
| `drop::consume_closure`, `drop::dec_shallow_io` | `Owned` |
| `trace::consume_trace_call` | `Owned` |

The closed public vocabulary remains `Owned::{from_abi, into_raw,
as_borrowed, raw_for_read, is_nullary_tag}` and
`Borrowed::{from_abi, to_owned, raw_for_read}` exactly as approved. `Owned` is
transparent, `#[must_use]`, neither `Copy` nor `Clone`, and has the accepted
debug-only, unwind-safe drop bomb. `Borrowed<'a>` is the copyable read view and
has no discharge operation. `free_io_node(i64)` remains raw because its input
has already reached RC zero and is not a live counted reference.

The delivered `SexpAnnotated` field disposal in
`crates/cranelisp-intrinsics/src/drop.rs` and the ABI-10 `Pure` ownership
witness/`free_io_node` disposal are inputs to this migration. Their tag tables,
dispositions and behavior are unchanged.

## 2. Intrinsics interior

Each nine-funnel entry consumes its `Owned` exactly once through `into_raw`
before its existing nullary guard or decrement. The raw RC and field-access
mechanisms below that point remain raw. `consume_vec_with` creates one `Owned`
per live element and passes it to its `fn(Owned)` callback. Its two private
callback producers are exactly `rc::consume_shallow` for Vec-of-String and
`drop::consume_io_tree` for Select's Vec-of-IO carrier; no callback alias is
published.

The existing Sexp and IO tag dispatchers stay separate because they own
different closed layouts and IO alone has a disposition. They share one
private `owned_field(base, offset)` operation in `drop.rs`, which reads a field
after the zero-observing decrement/fence and performs the raw-to-`Owned`
transfer. Together with the Vec element loop, these are the only two
raw-to-`Owned` mint sites in `drop.rs`. Recursive fields, SList tails, inline
Par branches and the Select carrier all flow through those sites. This keeps
the delivered exhaustive tag tables intact and preserves the intended
countable trusted base despite the two family-specific dispatchers now in
source.

Other intrinsics modules still contain raw ABI values or private raw owner
carriers. Adapt only at an existing source-stated ownership handoff; do not
reshape the trampoline, trace representation or callback ABIs in this stream.
The complete production caller allow-list is:

| Path | Existing owner seam that may construct `Owned` |
|---|---|
| `crates/cranelisp-intrinsics/src/io.rs` | `cranelisp_run_io`'s transferred input; `ProducedValue`'s armed Par buffer; `TrampolineFrame`'s fresh current/continuations; the async and synchronous fresh-Bind releases; `feed_continuation`; `call_continuation` |
| `crates/cranelisp-intrinsics/src/panic.rs` | the IO-valued `main_result` in `cranelisp_run_program`; the transferred thunk in `catch_runtime_error` |
| `crates/cranelisp-intrinsics/src/reactor.rs` | `StateClosure::consume`; the supervised strand's owned `sub_tree` release |
| `crates/cranelisp-intrinsics/src/trace.rs` | the six consuming extern accessors (`first_child_nanos`, `name`, `params`, `result`, `children`, `nanos`) and last-reference field/tail transfers inside TraceCall disposal |
| `crates/cranelisp-intrinsics/src/vec_runtime.rs` | `UnpublishedVecStrings::drop`, whose public constructor contract already says the input vector transfers one owned reference per element |

`ResultDisposer` remains the compiler-provided raw `extern "C" fn(i64)`
drop-glue address. It is distinct from `consume_vec_with`'s Rust callback and
does not change to `fn(Owned)`. Likewise, JIT closure calls, poll functions and
backend/platform emitted signatures remain raw. Outside those sites and the
approved D8 extension below, every `Owned::from_abi` use is a review rejection.
The existing
`mem::forget` allow-list remains `reactor.rs`'s C-waker transfer plus
`Owned::into_raw`.

The approved D8 extension adds three precisely guarded primitives uses to that
trusted base while leaving the intrinsics interior above unchanged:

| Use | Exact permitted primitives sites |
|---|---|
| Produced owner adoption | Delivered `crates/cranelisp-primitives/src/abi_facts.rs::adopt_produced_value` is the only direct adapter. Its callers are exactly 19 functions / 20 sites: `bool_to_string`; `float_to_string`; `int_to_string`; `parse_int`'s initialized `Some` and nullary `None`; `str_concat`; `str_substring`; one post-match `str_char_at`; `str_split`'s child String; `vec_strings_from_owned_handles`' completed Vec; `str_join`; `str_replace`; `str_trim`; `str_to_upper`; `str_to_lower`; completed `alloc_adt_2`; completed `alloc_adt_3`; `alloc_runtime_string`; `build_runtime_list`'s `SNil`; and `quote_sexp_build`'s existing post-`runtime_panic` raw-zero error sentinel. |
| Parent-lifetime child borrow | Delivered `crates/cranelisp-primitives/src/marshal.rs::borrowed_field` is the only adapter. Its six calls are `read_slist`'s `SCons` head/tail and `quote_sexp_build`'s `SexpStr`, `SexpSym`, `SexpList`, and `SexpBracket` payloads. Scalar Sexp payloads stay raw. |
| Owner transfer into raw storage | Exactly four `into_raw` calls: `marshal::alloc_adt_2`'s `StoredField::Owned` arm, both owned fields in `marshal::alloc_adt_3`, and `string::vec_strings_from_owned_handles`' element conversion after full raw-Vec capacity is prepared. |

`adopt_produced_value` accepts only a fully initialized fresh RC=1 value, the
named `None`/`SNil` result, or the existing no-reference error sentinel after
`runtime_panic`; it is not an arbitrary scalar-to-owner licence. ADT parents
are allocated and prepared before children are disarmed, and adoption follows
complete initialization. The Vec receiver retains typed child owners until
raw capacity is ready, then transfers without an intervening fallible step to
the existing guarded `vec_strings_from_owned`. `borrowed_field` narrows the raw
borrow to its live parent's lifetime and never mints an owner. Existing children
that enter a new result use `Borrowed::to_owned`; neither `sconcat`'s shared
tail nor quote's reused children enter the produced-owner adapter.

The verified structural guard permits the two delivered primitives adapters,
the four storage exits and Q3's intrinsics parent-borrow projection by exact
function/site, alongside the existing shim, intrinsics owner and `drop.rs`
sites. The Q3 projection has exactly two field uses. Whole-file or whole-crate
exemptions, disarm/re-adopt round trips, and additional callers remain review
rejections. The guard makes the unsafe assertions enumerable; it does not prove
the permitted raw words' provenance.

The caller census also finds the test fixture at
`crates/cranelisp-backend/src/compiler/control_flow/launch.rs`. The delivered
backend adaptation wraps its owned `cont_ptr` for `consume_closure`; the
compiled closure ABI and fixture logic do not change. Primitives is also
delivered; Binary/int remains a required consumer under §3, so this
fixture is not the complete cross-crate propagation set.

### Continuation-produced `Bind` ownership on normal completion

QA's module pair attributes Q3 to the fresh-`Bind` transition in both
trampoline bodies. Run `34c74925-ba8e-4e74-bdab-f9d63b7c2d60` records the
unique-parent control passing and the shared-parent subject returning `73` with
its parent live but both owned fields dead. This is a normal-completion breach
of `spec/12-runtime.md` §12.3.1. It does not establish that the public
`sequence-io` crash has the same concrete parent.

`current_is_fresh` means the trampoline owns one continuation-produced
reference. It does not mean the node has only one reference. Before descending
through a fresh `Bind`, the trampoline must establish its own references to the
inner IO node and continuation while its parent reference is still live, then
release that parent with structural `consume_io_tree`. The inner owner becomes
`frame.current`; the continuation owner enters `frame.cont_stack`. The disposer
word remains scalar metadata.

Always acquiring both field references before structural parent release is the
single rule for RC=1 and RC>1; the trampoline must not inspect the count to
choose an ownership story. With RC=1, structural teardown releases the parent's
two field references and the newly acquired references carry the traversal.
With RC>1, the retained parent keeps its field references and the traversal
later releases only the two references it acquired. The existing
`SpineTransferred` release remains correct for fresh nodes whose fields have
already transferred under their own established rules, but it is no longer the
fresh-`Bind` descent operation. This supersedes the `Bind` transfer statement in
`s121-c5-intrinsics-visit.md` §4.2.

The delivered shared `read_bind_transition` applies the transition once for the
synchronous and asynchronous dispatchers. It materializes the frame-owned parent as
`Owned`; one private parent-borrow projection narrows the existing
`Borrowed::from_abi` assertion to the live parent and immediately uses
`Borrowed::to_owned`, the approved single home of `rc_inc`. This adds one
precisely guarded intrinsics field-projection seam with exactly the inner and
continuation uses. It adds no handle operation and no direct `rc_inc` exception.
Non-fresh caller-tree `Bind` nodes retain the existing borrowed descent: no
child increment, no parent release, and the caller's final structural walk
remains their owner.

Cancellation needs no second correction. After fresh-`Bind` descent, the frame
owns the current node and every fresh continuation independently, so its
existing drop guard can discharge them if the future is cancelled. Normal
completion continues to discharge the same owners through
`feed_continuation`. No IO layout, disposer rule, emitted ABI, observer event,
or scheduling behavior changes. The Q3 production correction is confined to
`crates/cranelisp-intrinsics/src/io.rs`; `drop.rs` supplies the existing
structural consumer and needs no Q3 behavior change. The module evidence and
citation repair remain in `io/tests.rs`.

## 3. Dependencies and handoff

The intrinsics source steps are delivered: `handle.rs` and its module evidence,
the nine signatures, the typed Vec callback, the `drop.rs` field-transfer seam,
the named same-crate caller allow-list, and the shared fresh-`Bind` transition.
The recursive lexical guard now enforces the intended exact function/site
allow-list. Moving one approved adoption to a same-count unauthorized helper
was rejected in run `f328523a-868d-463d-a0ab-732cee761c7d`; the restored source
passed 1/1 in run `e0a1f21b`. The remaining intrinsics-owned artifact is to
regenerate `crates/cranelisp-intrinsics/public-api.txt` and confirm that its diff
contains exactly the approved additions and replacements in §1.

The primitives consumer is delivered under
`design/primitives/s122-typed-consume-consumers.md`; it consumes the handle and
nine-funnel producer plus the exact D8 guard above without changing this crate's
public target. The backend fixture adaptation named in §2 is also delivered.
Binary/int still has to consume the runtime vocabulary in
`src/{marshal,expander}.rs`; its executable-code lease remains separate from
heap ownership. This consumer tail, the integrated macro/public evidence and
the raw committed baseline prevent a claim that the total
typed funnel or its integrated macro/public evidence is complete.

## 4. Evidence and review gates

- Delivered `crates/cranelisp-intrinsics/src/handle/tests.rs` carries the approved
  drop-bomb triplet: a deliberate leak fires with the located prefix; the same
  fixture consumed through `consume_shallow` is silent and balanced; an
  unrelated unwind remains survivable. Each positive leg is observed against
  the corresponding planted break before credit.
- Existing drop, RC, diagnostic, trace, Vec, reactor and IO tests receive only
  ownership-construction/type adaptations unless a current assertion exposes
  a real behavior change. Existing annotated-Sexp and ABI-10 IO disposal
  evidence stays the behavior oracle; it is not recreated.
- The generated public baseline must show the approved handle additions and
  exactly nine signature replacements, including inline `fn(Owned)`. Any other
  public line or consumer edge returns to architecture and the user.
- The recursive exact function/site source allow-list and the two `mem::forget`
  occurrences are mechanical review gates. The same-count unauthorized-helper
  plant proves the function mapping detects a moved adoption, while recursive
  source discovery covers nested modules. This remains a lexical structural
  guard: it makes approved sites enumerable but does not prove raw-word
  provenance or semantic correctness inside an allowed function.
  D8 adds separate prohibited-caller plants and valid controls
  for produced adoption, parent-lifetime borrowing and storage exits. A mint,
  projection or exit outside the exact named seams, a public callback alias,
  or a change to raw emitted ABI is a rejection.

ACT-0956 now has one deterministic module test in
`crates/cranelisp-intrinsics/src/io/tests.rs`. The test first polls
`run_blocking_branch` through admission/spawn to `Pending` on its oneshot
receiver. A branch-local `#[cfg(test)]` post-send barrier at the existing
publication point blocks the worker only after `tx.send` succeeds. Without
polling the now-ready receiver again, the test drops the Select-loser future,
then releases and joins the worker, and proves the queued nonzero-disposer
payload was released with its exact value exactly once. A scope guard releases
the barrier and permits worker completion if an assertion unwinds, so this test
cannot strand rayon work or contaminate another test. A winner control polls
the same ready handoff, transfers the result, observes no disposal before
caller release, then exactly one after caller release. This is module evidence
for the existing RAII path: no wall-clock-only oracle, e2e case, runtime
mechanism or public test seam is added.

Q3 reuses
`continuation_returned_unique_bind_transfers_and_balances` and
`continuation_returned_shared_bind_preserves_retained_parent_fields`. The first
must keep returning `73`, free the unique parent and fields, and balance. The
second must return `73`, observe the retained parent and both fields live before
final release, then balance after releasing that parent. The already-recorded
pass/RED pair arms these assertions against the missing child-reference
acquisition. Retain the existing deep-Bind and cancellation-drop-guard checks;
no new cancellation matrix is allocated.

The retained intrinsics dev visit repaired both module comments to cite
`spec/12-runtime.md` §12.3.1, because these tests exercise ordinary reachability
and teardown rather than cancellation. The module pair passes in focused run
`c302a849-f90c-4654-8b2c-6b7e16ae5d11`; this is attribution evidence. Rerun the
already-allocated public two-nested-action `sequence-io` subject and its exact
aggregate, explicit-bind, one-action, empty and two-Pure controls in REPL,
`--run`, and `--link`. Public success remains acceptance evidence rather than
module attribution: if it stays red, return it to QA for reattribution instead
of widening this correction.

## 5. Public and operational effects

There is no new public delta beyond the already-approved target in §1. D8 and
the Q3 fresh-`Bind` correction are private and add no baseline row. The
current raw baseline is a pending generated-artifact update, not the delivered
source surface. `cranelisp-primitives`
has no planned Rust-baseline change because its bodies and generated shims are
private. Emitted C ABI, intrinsic names/arities, heap layout, platform ABI,
cache schema and deployment behavior are unchanged.

Focused run `c302a849-f90c-4654-8b2c-6b7e16ae5d11` passes all eight allocated
handle, Q3 and Q11 rows. The trusted-base guard is additionally armed by the
same-count move RED `f328523a-868d-463d-a0ab-732cee761c7d` and restored 1/1
GREEN `e0a1f21b`, within the lexical limit above. The sandbox-wide run
`f9a7fbea` passes 346/349; its three reactor
socket rows timed out in the sandbox, then passed 3/3 under the authorized
environment in run `88059622-c822-4350-89c6-927605ad3ead`. Handle-bomb deletion
and unwind-clause plants establish those module instruments' detection ability.
These results do not establish the still-pending public `sequence-io`,
macro-transfer or downstream-consumer acceptance.
