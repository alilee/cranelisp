---
number: 0638
target: /qa
filed_by: /sprint
filed_at: 2026-07-17
sprint_filed: 111
refers_to: stdlib/derive.cl (derive-Eq/Ord/Display invocation);
  stdlib/derive/helpers.cl (dt-body returns `rest`, an interior tail of `dt`);
  crates/cranelisp-intrinsics/src/alloc.rs:222/:384 (double free / dealloc);
  S111 /stdlib 0614 downstream finding; repro saved (scratchpad, EPHEMERAL — see below)
status: open
---

# Macro-expansion invocation double-free — helper returning a deep interior alias corrupts on the JIT macro-clause path

## The defect (reachable memory-safety — double free / SIGSEGV)

After 0614 (S111) moved derive's helpers to a dependency module, `derive-Eq`/`derive-Ord`/
`derive-Display` **compile** but **double-free at invocation**:
```
(derive-Eq (deftype Color Red Green Blue))
=> thread 'priority-worker-0' panicked at crates/cranelisp-intrinsics/src/alloc.rs:222:
   double free or invalid free at 0x...  (runtime/dealloc, alloc.rs:384)
```
NOT a §9.3.4 issue and NOT the 0614 restructuring: the identical helper logic works via a plain
cross-module function call in `--run` (exit 3, correct). The fault is **specific to the
macro-expansion invocation path** (JIT-invoked macro clause + Sexp marshalling) combined with
helpers that **match their argument multiple times and return a deep interior alias** — `dt-body`
returns `rest` (an interior tail of `dt`) while `dt` is also matched by `dt-has-docstring`.
Class: `uaf`/`rc-miscount` (double-free). **Plausibly a sibling of the S111 0633 drop-glue /
§3.7 COW-UAF interior-alias family** — same "interior alias whose ownership fact is wrong →
double free/UAF" shape, on the macro-clause JIT path.

## Minimal deterministic repro (PRESERVE — scratchpad is ephemeral)

`/stdlib` saved `dthelp.cl` + `mac.cl` + `usemac.cl` to the session scratchpad
(`.../scratchpad/DEFECT-repro/`): a macro whose body calls a dependency-module helper that
returns an interior alias, then an allocating `smap` over it → `--run usemac.cl` aborts with
the double-free. Uses only `primitives` + the synthetic `macros` module + two tiny local modules.
REPL also corrupts. **`/testing` must re-capture this into `tests/` before the scratchpad clears.**

## Requested action

`/qa` **attribution** (per `tests/CLAUDE.md` §"Isolating Cross-Crate Failures"): is the root the
**same** as §3.7 COW-UAF (→ likely fixed by CS-5's `MayAliasOf` + truthful-facts ownership work)
or 0633 drop-glue (→ CS-1.1 re-key), or a **distinct** macro-clause-marshalling defect? Then:
1. `/testing` lands a narrow failing-not-ignored repro from the saved files (all three modes),
   `// defect: class=uaf|rc-miscount ... found=S111 owner=/dev`.
2. **Re-check the repro AFTER CS-5 lands** — if the §3.7 ownership fix cures it, add the
   regression row and attribute to §3.7; if it survives, it is a distinct interior-alias defect
   → compiler-skill fix (`/dev` backend/intrinsics), fix-vs-carry = `/sprint` call.

Sequencing note: this is the "0605 tier-2 follow-on" FIXME 0614 deferred — now a LIVE
memory-safety defect, not merely missing derive-invocation coverage.

## Preserved repro (verbatim from the ephemeral scratchpad — `--run usemac.cl` double-frees)

`dthelp.cl` (helper module — `dt-body` returns `rest`, an interior tail alias):
```clojure
(import [prelude []])
(import [primitives [add-i64 sub-i64 eq-i64]])
(import [macros [*]])

(defn sfold [f init xs]
  (match xs [SNil init (SCons h t) (sfold f (f init h) t)]))
(defn sreverse [xs] (sfold (fn [acc x] (SCons x acc)) SNil xs))
(defn smap [f xs] (sreverse (sfold (fn [acc x] (SCons (f x) acc)) SNil xs)))
(defn sdrop [n xs]
  (if (eq-i64 n 0) xs
    (match xs [SNil SNil (SCons _ t) (sdrop (sub-i64 n 1) t)])))

(defn dt-head [dt]
  (match dt
    [(SexpList items)
     (match items [(SCons _ tail1) (match tail1 [(SCons head _) head _ (SexpSym "e")]) _ (SexpSym "e")])
     _ (SexpSym "e")]))
(defn dt-has-docstring [dt]
  (let [third (sdrop 2 (match dt [(SexpList items) items _ SNil]))]
    (match third [(SCons elem _) (match elem [(SexpStr _) true _ false]) _ false])))
(defn dt-name [dt]
  (let [head (dt-head dt)]
    (match head [(SexpSym s) s (SexpList items) (match items [(SCons first _) (match first [(SexpSym s) s _ "e"]) _ "e"]) _ "e"])))
(defn dt-body [dt]
  (match dt
    [(SexpList items)
     (match items
       [(SCons _ tail1)
        (match tail1 [(SCons _ rest) (if (dt-has-docstring dt) (match rest [(SCons _ ctors) ctors _ SNil]) rest) _ SNil])
        _ SNil])
     _ SNil]))
(defn dt-constructors [dt]
  (let [body (dt-body dt)]
    (match body
      [(SCons first _)
       (match first [(SexpBracket _) (SCons (SexpList (SCons (SexpSym (dt-name dt)) body)) SNil) _ body])
       _ SNil])))

(defn slen [xs] (sfold (fn [acc _] (add-i64 acc 1)) 0 xs))
```

`mac.cl` (macro whose body returns the interior alias then allocates over it):
```clojure
(import [prelude []])
(import [primitives [add-i64]])
(import [macros [*]])
(import [dthelp [dt-constructors smap slen]])

(defmacro count-ctors [dt]
  (SexpInt (slen (smap (fn [x] x) (dt-constructors dt)))))
```

`usemac.cl` (`--run` this → double-free at `alloc.rs:222`):
```clojure
(import [primitives [Pure]])
(import [mac [count-ctors]])

(defn main []
  (Pure (count-ctors (deftype Color Red Green Blue))))
```
