# Live development — redefining functions in a running session

The REPL is a live development environment: you define a function, call it, see
the result, and redefine it — without restarting, and without your other
definitions disappearing. This page is the practical guide to what happens when
you redefine something that other code already depends on. The normative
contract is [`repl/spec.md §18`](../../repl/spec.md); this page re-presents it
for everyday use.

Two kinds of redefinition behave very differently, and the split is the key to
everything below:

- **Body edits** (the signature stays the same) just take effect — quietly.
- **Signature changes** ripple: the session recompiles the functions that
  depend on the changed one, and tells you exactly which survived and which
  did not.

> **About the transcripts.** Every transcript on this page was checked against
> the real binary. The prompt's timing prefix (`3+0ms; user>`) is elided to
> `user>` for readability. The examples import primitives explicitly
> (`add-i64`, `mul-i64`, `str-len`) so they run in *any* directory, with or
> without the standard prelude on the search path — with the prelude loaded you
> would write `+` and `*` instead.

## Body edits just take effect

Redefine a function without changing its type and the new body is simply live —
for everybody, immediately:

```
user> (import [primitives [add-i64]])
user> (defn f [x] (add-i64 x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (g 1)
:primitives/Int 2

user> (defn f [x] (add-i64 x 10))    ; body edit — same signature
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (g 1)
:primitives/Int 11
```

Three things to notice:

- **No noise.** The redefinition turn prints the ordinary confirmation and
  nothing else — no report, because there is nothing to reconcile. `g` was
  compiled against `f`'s *signature*, and that did not change.
- **Late binding.** `g` was not recompiled, yet it picks up the new body on its
  next call. So does every other route into `f` — functions that call it,
  function values created earlier, partial applications. This is the prized
  REPL semantic: edit the body, and the whole session sees the fix.
- **Cost stays flat.** A body edit recompiles one symbol, no matter how many
  callers it has.

The normative pin is [`repl/spec.md §18.2`](../../repl/spec.md).

## Changing a signature — the cascade report

When a redefinition changes the function's *type*, its compiled callers were
built against assumptions that no longer hold. The session immediately
re-typechecks and recompiles everything that depends on the changed symbol
(dependents of dependents included), and the turn reports the outcome:

```
user> (import [primitives [add-i64 mul-i64 str-len]])
user> (defn f [x] (add-i64 x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (defn k [x] (f (mul-i64 x 2)))
:(Fn [primitives/Int] primitives/Int) user/k ; defn

user> (defn f [s] (str-len s))       ; signature change: Int -> Int becomes String -> Int
:(Fn [primitives/String] primitives/Int) user/f ; defn
; recompiled:
;  g
; broken:
;  k — type error at 12..29: type mismatch: expected primitives/String, got primitives/Int
```

Read the report like this:

- **`recompiled:`** lists the dependents that still typecheck under the new
  signature and were rebuilt against it. `g`'s body passes its argument
  straight through, so it survives — and its own signature is now
  `(Fn [primitives/String] primitives/Int)`. Recompiled callers are fully in
  the new world:

  ```
  user> (g "hello")
  :primitives/Int 5
  ```

- **`broken:`** lists the dependents that no longer typecheck, each with the
  type error that broke it. `k` multiplies its argument before passing it to
  `f`, pinning it to `Int` — under the new `f` that is a type error, so `k`
  cannot be rebuilt.
- **Empty sections are omitted.** A signature change with no compiled
  dependents prints only the ordinary confirmation, exactly like a body edit.
- **Nothing else stops.** A broken symbol is ordinary session state, not an
  error mode: every other definition keeps working, and only calls that
  actually reach the broken symbol fail (see [the trap](#calling-a-broken-symbol-the-trap)).

The full contract — exact-set guarantees, report layout — is
[`repl/spec.md §18.3`](../../repl/spec.md).

## Broken symbols know why they are broken

A broken symbol is not gone. Its metadata — last-good signature, docstring,
source — is intact; only its compiled code is. Ask it, any way you like, and it
tells you what broke it:

```
user> /sig k
:(Fn [Int] Int) k ; defn
; broken by the redefinition of user/f: type error at 12..29: type mismatch: expected primitives/String, got primitives/Int

user> /info k
:(Fn [primitives/Int] primitives/Int) user/k ; defn
; broken by the redefinition of user/f: type error at 12..29: type mismatch: expected primitives/String, got primitives/Int
  (defn k [x] (f (mul-i64 x 2)))

user> k
:(Fn [primitives/Int] primitives/Int) user/k ; defn
; broken by the redefinition of user/f: type error at 12..29: type mismatch: expected primitives/String, got primitives/Int
```

- The type shown is the **last successfully compiled signature** — what `k`
  was, before the break.
- The provenance line always has the same shape:
  `broken by the redefinition of {cause}: {original error}` — the symbol whose
  redefinition broke this one, plus the exact type error. You never have to
  reconstruct *why* from memory.
- `/info` additionally shows the definition source — handy for deciding how to
  fix it — and deliberately shows no code-size statistics: there is no compiled
  code to measure.
- **Being broken does not spread.** Callers *of* a broken symbol are not marked
  broken — their compiled code is still valid. They simply hit the trap at
  runtime if a call actually reaches the broken symbol.

Normative details: [`repl/spec.md §18.4`](../../repl/spec.md).

## Calling a broken symbol — the trap

A broken symbol refuses to run, loudly and with the same provenance:

```
user> (k 3)
runtime error: user/k is broken by the redefinition of user/f: type error at 12..29: type mismatch: expected primitives/String, got primitives/Int
```

The trap is presented through the ordinary runtime-error format (§5.1) — the
`runtime error:` category followed by the provenance message — so it reads the
same as any other runtime failure the REPL surfaces.

This is a deliberate design ruling, not a limitation. The session *could* keep
serving `k`'s old compiled code — it would be memory-safe — but silently
running code that no longer matches the source you just changed is the worse
experience. So a broken symbol **fails loud, with provenance, recoverably**:

- **Every route traps** — direct calls, calls from compiled callers, function
  values and partial applications created before the break.
- **The session survives.** The trap is an ordinary runtime error: the REPL
  prints it and carries on. Everything else remains callable, and you can trap
  as many times as it takes you to get around to the fix.

Normative details: [`repl/spec.md §18.5`](../../repl/spec.md).

## Recovery — fix either end

Broken-ness is repaired by redefinition, in whichever direction matches your
intent. Each redefinition re-runs the same recompile-dependents transaction.

**Fix the broken symbol** — you meant the change; update the caller to match:

```
user> (defn k [s] (f s))             ; k now takes the String that f wants
:(Fn [primitives/String] primitives/Int) user/k ; defn

user> (k "abc")
:primitives/Int 3

user> /sig k
:(Fn [String] Int) k ; defn
```

**Revert the cause** — the change was a mistake; put the signature back:

```
user> (defn f [x] (add-i64 x 1))     ; put f back
:(Fn [primitives/Int] primitives/Int) user/f ; defn
; recompiled:
;  g k

user> (k 3)
:primitives/Int 7
```

The broken symbol is still a registered caller of `f`, so it rejoins the
transaction automatically and comes back green in the `recompiled:` section —
no need to re-enter it. Either way, a recovered symbol is indistinguishable
from one that was never broken: it calls normally and carries no provenance
line. ([`repl/spec.md §18.6`](../../repl/spec.md).)

### A failed turn is discarded as a whole

The same safety boundary applies when failure happens later, during code
generation rather than ordinary typechecking. The diagnostic names the actual
definition that failed. None of that turn's definitions, compiled entries, or
introspection rows become live, and the failure is not retried when you enter
the next expression.

That means you can evaluate an unrelated value immediately, or enter a clean
definition with the failed name, without restarting the REPL or clearing
hidden state. This is the atomic failed-turn guarantee in
[`repl/spec.md §18.4`](../../repl/spec.md). There is intentionally no worked
failure recipe here: the current production trigger is itself a known compiler
defect, not a language technique users should learn.

## Which world does an old value see?

The two redefinition classes give two deliberately different answers for
values that already exist when the redefinition lands:

- **Body edits: late binding.** Every existing value and caller sees the new
  body at its next call (as shown [above](#body-edits-just-take-effect)).
- **Signature changes: the frozen world.** Recompilation can reach everything
  callable *by name*, but a function value already sitting on the heap embeds
  direct pointers into the old code. Rather than let it make an unsound
  mixed-signature call — or invalidate live values mid-flight — the old chain
  is kept **frozen**: a closure created before the signature change, invoked
  after it, sees the *old* definitions all the way down, consistently. It will
  not crash, and it will never observe a mix of old and new.

By-name calls always see the current world — that is what the cascade report
describes. Frozen behaviour is reachable only through values you created
before the change, and it is a session-memory artifact only: frozen chains die
with the session, and a restart rebuilds everything from source in the current
world. The precise contract is [`repl/spec.md §18.7`](../../repl/spec.md).

## Redefining an impl

A trait implementation is a body you edit too. Re-entering an `impl` for a
(trait, type) pair that already has one **replaces** it — the whole
implementation, not just the methods you happened to retype — and subsequent
dispatch reaches the new bodies at the next call.

This is a **body edit at the dispatch layer**, so it behaves like one: each
method's compiled signature is the trait's declared signature for that type
(conformance is what makes the form legal at all), so nothing downstream needs
recompiling. No cascade report, no ceremony, and the confirmation line is the
ordinary one — there is no "redefined" marker, because *this is the impl now* is
the whole story:

```
user> (import [primitives [add-i64 mul-i64 sub-i64]])
user> (deftype Box [:Int w :Int h])
:(Fn [primitives/Int primitives/Int] user/Box) user/Box ; deftype

user> (deftrait Sizeable (size [x] Int) (tag [x] Int))
:user/Sizeable ; deftrait
; defn:
;  size tag

user> (impl Sizeable Box (defn size [b] (match b [(Box w h) (mul-i64 w h)])) (defn tag [b] 7))
impl user/Sizeable for user/Box

user> (size (Box 3 4))
:primitives/Int 12

user> (impl Sizeable Box (defn size [b] (match b [(Box w h) (add-i64 w h)])) (defn tag [b] 7))
impl user/Sizeable for user/Box

user> (size (Box 3 4))
:primitives/Int 7
```

### Replacement is wholesale

The unit of replacement is the **whole implementation for the pair**, never the
individual method. Two things follow.

**A re-`impl` must still implement the trait on its own.** Leaving out a required
method is not "keep the old one" — the replacement, taken alone, does not
implement the trait, so it is rejected by the ordinary conformance error:

```
user> (impl Sizeable Box (defn size [b] (match b [(Box w h) (sub-i64 w h)])))
Error: type error at 0..71: impl Sizeable for Box: missing required method tag
```

**Introspection reports what dispatches, not the history.** However many `impl`
forms you entered for a pair, `/info` on the trait lists exactly one entry:

```
user> /info Sizeable
:user/Sizeable ; deftrait
; defn:
;  size tag
; impl:
;  Box
  (deftrait Sizeable
    (size [x] Int)
    (tag [x] Int))
```

### A rejected re-`impl` changes nothing

Whether it fails on completeness (a missing method, above) or on conformance (a
body that does not typecheck against the declared signature), a rejected
re-`impl` leaves the **previous implementation installed and dispatching**. You
are never left with the pair half-replaced or emptied — the next call returns
exactly what it returned before:

```
user> (impl Sizeable Box (defn size [b] "nope") (defn tag [b] 7))
Error: type error at 19..41: type mismatch: expected primitives/String, got primitives/Int

user> (size (Box 3 4))
:primitives/Int 7
```

> **Read that message backwards.** The trait declares `size` returning `Int` and
> the body returns a `String`, so the message you want is *expected Int, got
> String* — the emitted text has the roles the other way round, and names neither
> the trait, the method, nor the fact that this is an impl-conformance failure.
> The rejection is right; only the wording is misleading. Tracked as FIXME 0806;
> the [errors catalogue](../errors/trait-impl-diagnostics.md#an-impl-method-does-not-conform-to-the-trait-signature)
> carries the same warning.

Persistence follows the same rule: the backing file keeps the **latest** `impl`
for the pair and only that one, so a restart reproduces the session that was
dispatching rather than replaying your edits. A rejected re-`impl` is never
written.

> **Default methods are outside this guarantee today.** A trait
> [default method](traits.md#default-methods--a-body-instead-of-a-return-type)
> whose body calls a **sibling** method of the same trait does not survive a
> re-`impl` of that trait for the type: the sibling call fails to link and the
> error points inside the `deftrait`, which is not where you changed anything.
> Each half is fine alone — defaults work, re-`impl` works — only the combination
> is broken. Tracked as FIXME 0832.

The normative pins are [`repl/spec.md §18.9`](../../repl/spec.md) (what you see)
and [`spec/05-definitions.md §5.4.5`](../../spec/05-definitions.md) (what is
legal).

## Beyond concrete functions — silent reloads and the remaining gaps

The cascade report, broken marking, and the trap are the story for a **concrete
single-signature function** (a plain `defn` with one
monomorphic type, like every example on this page, which is why they use
concretely-typed primitives such as `add-i64`). Redefining anything else takes
a different path, and after the S103 fix those paths split in two: generic and
overloaded functions are now recompiled for you; macros and types are not.

### Generic and overloaded functions — now recompiled, silently

Redefining a function whose type is **generic or overloaded** used to leave
existing compiled callers silently running the old definition. That is now
fixed. At the end of the turn the session reloads the affected module,
recompiling every compiled caller against the new definition, so the caller
picks it up at its next call. There is **no cascade report** — the recompile is
silent, exactly like a body edit — because the reload leaves nothing stale to
announce:

```
user> (import [primitives [add-i64]])
user> (defn f [x] (add-i64 x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (g 1)
:primitives/Int 2

user> (defn f [x] x)                 ; concrete -> generic — g is recompiled silently
:(Fn [a] a) user/f ; defn

user> (g 1)                          ; picks up the new f
:primitives/Int 1
```

Note the shape of the cure: `(g 1)` now returns `1`, not `2`. Under the old
behaviour `g`'s compiled code still called the old `f` and returned `2`; the
reload has moved `g` into the new world. The redefinition turn prints only its
ordinary confirmation — no `recompiled:` line, no `stale:` section.

**The one loud edge — a reload that can't typecheck.** If the redefinition
leaves a compiled caller genuinely ill-typed — the sharpest case is a concrete
function becoming *overloaded* in a way that makes an unannotated caller
ambiguous — the reload cannot recompile it. Rather than answer with the old
chain silently, the turn prints the interim `; stale:` section, and then blocks
evaluation until you repair the source:

```
user> (import [primitives [add-i64 str-len]])
user> (defn id [x] x)
:(Fn [a] a) user/id ; defn

user> (defn g [:primitives/Int y] (id (add-i64 y 1)))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (g 1)
:primitives/Int 2

user> (defn id [:primitives/String s] (str-len s))   ; downgrade leaves g's call ambiguous
:(Fn [primitives/String] primitives/Int) user/id ; defn
; stale: compiled callers keep the previous definition of user/id
;  g

user> (g 5)
Cannot evaluate: module 'user' has errors. Fix the source file and save.

user> (defn g [:primitives/Int y] (add-i64 y 100))   ; repair the caller — the block lifts
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (g 5)
:primitives/Int 105
```

The block is the [§14.4](../../repl/spec.md) error-blocked state, and it is
recoverable: redefining `g` (or reverting `id`) so the module typechecks again
lifts it, and the session carries on. The split world is **surfaced, never
silently answered**.

### Macros and types — still stale, silently

Redefining a **macro**, a **type**, or a **constructor** is still on the legacy
path: no reload, no report. An existing compiled caller keeps the **old**
expansion or layout — consistent and crash-free, but silently stale:

```
user> (import [primitives [add-i64]])
user> (defmacro m [x] `(add-i64 ~x 1))
:user/m ; defmacro
; [x] -> Sexp

user> (defn g [x] (m x))             ; g compiles the OLD expansion into its body
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (g 1)
:primitives/Int 2

user> (defmacro m [x] `(add-i64 ~x 100))   ; redefine the macro — silent
:user/m ; defmacro
; [x] -> Sexp

user> (g 1)
:primitives/Int 2                    ; g still runs the OLD expansion (x + 1)

user> (m 5)
:primitives/Int 6                    ; a fresh expansion sees the new macro
```

`(g 1)` returns `2`, not `101` — `g` was compiled with the old `m` already
expanded into its body, and nothing re-expands it. Types and constructors
behave the same way; a constructor **arity** change is the sharpest case
(`(Box [x])` → `(Box [x y])` leaves an old caller building the old shape) and
is tracked as FIXME 0533.

This is a scoped, documented limitation — the scope note in
[`repl/spec.md §18.1`](../../repl/spec.md) is the authoritative statement, and
closing it is planned work. Until then: after redefining a macro or type,
redefine (or reload) the callers you want to move to the new world, or restart
the session — a restart rebuilds everything from source.

### Cache restoration does not change macro expansion

The recompilation limitation above is about editing a macro in a live session,
not about the on-disk compile cache. An unchanged program using a user-defined
macro has the same result with a cold cache and after restoration, in REPL,
`--run`, and `--link`. You do not need a cache-specific macro definition or a
`--no-cache` workaround for ordinary macro use.

There are two narrower open cache defects to know about:

- A cache-restored parent currently may not enrol a declared private child, so
  `/run-tests parent.test` can find the test module on a fresh load but not a
  warm one ([FIXME 0868](../../design/arch/fixmes/0868-cache-restored-parent-does-not-enrol-private-child.md)).
- When one child module owns a trait and a sibling writes its impl, a fresh
  `--run` can dispatch successfully while the unchanged warm run loses that
  impl ([FIXME 0869](../../design/arch/fixmes/0869-cache-restoration-loses-sibling-written-trait-impls.md)).

These are known fresh/cache divergences, not intended module or trait rules.
For affected Run workflows, `--no-cache` forces recompilation; Link mode does
not accept `--no-cache`. No fix schedule is promised here.

### Known `def` presentation gap

The standard library's `def` is a macro, not a core special form. Today the
REPL can expose that implementation: its confirmation may name a generated
`*-def` thunk, and `/info` or `/sig` may classify the public binding as a
macro instead of describing its value. A function value bound with `def` also
has a separate unresolved application question.

This is known, unintended presentation behavior tracked by
[FIXME 0800](../../design/arch/fixmes/0800-def-macro-expansion-leaks-internal-thunk-name-and-blocks-call.md).
The rejected local correction did not ship; the proposed compiler transaction
is recorded in
[FIXME 0863](../../design/arch/fixmes/0863-cluster-wide-prepared-macro-presentation-transaction.md).
Do not rely on the generated thunk name—it is not a user API.

## Restarting with a broken symbol in the file

The REPL persists your definitions to the entry module's source file as you
work, including a broken symbol's source — the file always reflects the latest
thing you wrote, and broken-ness itself is session state, never written to
disk. That has one consequence to know about: if you quit while a symbol is
broken, the backing file *as a whole* no longer typechecks. Today the restart
reports exactly that and exits before the prompt:

```
$ cranelisp
user.cl:1:1: error: module error at 0..0: module 'user' failed: type error at 87..104: type mismatch: expected primitives/String, got primitives/Int
```

The recovery is to fix the inconsistency in the source file directly (it is
ordinary Cranelisp source — edit `user.cl`, aligning the caller or the callee
just as you would at the prompt) and start again. The specified direction is
friendlier — the session should start anyway, show the error, and let you
repair it at the prompt — see [`repl/spec.md §18.8`](../../repl/spec.md) for
the floor and where it is heading. The other half of the guarantee already
holds: the on-disk compile cache never captures a broken symbol's trap as if
it were real code, so a restart can never silently serve stale code for a
definition you broke.

## Cross-links

- **Normative contract** — the full redefinition semantics:
  [`repl/spec.md §18`](../../repl/spec.md).
- **Session persistence** — how the entry file is regenerated and restored:
  [`repl/spec.md §15`](../../repl/spec.md).
- **REPL basics** — [`getting-started.md`](../getting-started.md).
