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
Error: codegen error at 0..0: runtime error: runtime panic: user/k is broken by the redefinition of user/f: type error at 12..29: type mismatch: expected primitives/String, got primitives/Int
```

(The `Error: codegen error at 0..0: runtime error: runtime panic:` prefix is a
known wrapper defect being cleaned up; the message that matters is the
`user/k is broken by the redefinition of user/f: …` trap itself.)

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

> If you have evaluated bare expressions since the break — `(g "hello")` or
> `(k 3)` above — a cascade report may today also name `__expr`, the REPL's
> internal slot for your most recent expression turn. It is cosmetic noise
> (internal names do not belong in the report) and a defect has been filed to
> drop it.

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

## What the cascade doesn't cover yet

The dependent-recompilation machinery above currently engages only when the
redefined symbol is a **plain function with one concrete signature** (like
every example on this page — which is why they use concretely-typed primitives
such as `add-i64`). Redefining anything else — a generic or overloaded
function, a macro, a type, a trait — takes the legacy path: no cascade report,
and no broken marking. Existing compiled callers then keep running the **old**
definition chain — consistent and crash-free, but silently stale:

```
user> (defn f [x] (add-i64 x 1))
:(Fn [primitives/Int] primitives/Int) user/f ; defn

user> (defn g [x] (f x))
:(Fn [primitives/Int] primitives/Int) user/g ; defn

user> (defn f [x] x)                 ; concrete -> generic: no cascade runs
:(Fn [a] a) user/f ; defn

user> (g 1)
:primitives/Int 2                    ; g still runs the OLD f (x + 1)

user> (f 5)
:primitives/Int 5                    ; direct calls see the new f
```

Note the shape of the residue: `(g 1)` returns `2`, not `1` — `g`'s compiled
code still calls the old `f`. Redefine `g` itself (or restart the session) and
it picks up the new world. This is a scoped, documented limitation of the
current stage — the scope note in [`repl/spec.md §18.1`](../../repl/spec.md)
is the authoritative statement, and closing it is planned work. Until then: if
you want the cascade report to have your back, keep the functions you are
actively reshaping on concrete signatures.

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
