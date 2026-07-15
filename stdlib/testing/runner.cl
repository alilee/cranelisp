;; testing/runner.cl — In-language test runner over discovered test pairs
;;
;; Realises design/arch/test-discovery.md §4.3/§5/§6 (FIXME 0273): an ORDINARY
;; map/filter runner over the fn-value pairs `discover-tests` returns. No macro
;; runner — the freshness lives in the late-bound callables, so plain `vec-map`
;; over a fresh `(discover-tests)` call always sees the current test set
;; (ruling 1, the composability decision).
;;
;; The two language constructs this composes:
;;   discover-tests       :: (Fn [(Vec String)] (Vec (Pair String (Fn [] (Option String)))))
;;   catch-runtime-error  :: forall a. (Fn [(Fn [] a)] (Result a String))
;;
;; A test is an ordinary zero-arg fn whose name begins `test-` and whose type is
;; exactly `(Fn [] (Option String))` — None = pass, (Some why) = assertion fail.
;; `discover-tests` returns only the eligible (correctly-typed) `test-*` fns.
;;
;; Per-test three-way fold (the payoff of the two rulings composing):
;;   (catch-runtime-error run) :: (Result (Option String) String)
;;     (Err msg)        — the test PANICKED (match non-exhaustion, /0, oob, …)
;;     (Ok None)        — the test PASSED
;;     (Ok (Some why))  — the test ran and reported an assertion FAIL
;;
;; match-shape NOTES (informed by this sprint's verification on the prebuilt
;; binary — see the sprint report):
;;   * match arms are a SINGLE bracket of alternating `pattern body` pairs
;;     (spec §6.1 — `'[' match_arm+ ']'`); separate per-arm brackets do NOT parse.
;;   * constructor patterns bind SYMBOLS only (spec §6.2.1 — `'(' symbol symbol* ')'`);
;;     a NESTED ctor pattern like `(Ok (Some why))` is NOT grammar. The three-way
;;     fold is therefore a NESTED match (outer Result, inner Option).
;;   * `vec-reduce` is currently mis-inferred (over-unified to (Vec a) everywhere),
;;     so the tally/report folds use explicit tail-recursive loops over vec-len /
;;     vec-get instead. `vec-map` / `vec-filter` infer correctly and are used.
;;
;; RUNTIME SCOPE. `discover-tests` is a host-promised extern (DefKind::PrimitiveExtern)
;; resolved only in a LIVE REPL session — so `run-all` / `run-matching` (and any code
;; that references `discover-tests`) run in the REPL, but NOT when this module is
;; compiled as a `--run`/cache dependency object (the object linker has no host symbol;
;; test-discovery.md §4.5 dev-session-only framing). The pure helpers below
;; (run-one / present-one / tally / report / passed?) work in every mode.
;;
;; SELF-TESTS now ship as a `(mod- test …)` submodule again (S82 Phase 6). Two
;; defects that S81 had to route around are FIXED: a parent→child `super` import
;; resolves the parent's symbols (0342, int load-ordering), and loading a module
;; whose source carries a `(mod test …)` body no longer clobbers the backing
;; `.cl` on source-regen (0343, entry-module role-gate). The submodule imports
;; the runner's parent helpers via `super` and asserts with `assert-true`/
;; `assert-false` AND `assert-eq`.
;;
;; S83 Phase 6 (0355): `assert-eq` is RESTORED here. A cross-module call of a
;; stacked-trait-bound fn (`assert-eq`'s `[:Eq :Display a :Eq :Display b]`,
;; imported from `testing.assertions` and called from this `test` submodule)
;; now monomorphises in the defining module's scope and RUNS to completion —
;; where it previously SIGSEGV'd (the resolved FIXME 0354/0355). These
;; assert-eq self-tests are the durable stdlib-side regression guard for that
;; cross-module constrained-call path.
;;
;; Spec: design/arch/test-discovery.md §4.3/§5/§6, plan-stdlib.md §3.3

(import [prelude []])

(import [primitives [discover-tests catch-runtime-error
                     Int Bool String Pair Option Some None Result Ok Err
                     str-concat int-to-string add-i64 eq-i64 ge-i64
                     vec-len vec-get]])
(import [collections.vec [vec-map vec-filter]])
(import [collections.pair [first second]])
(import [text.string [index-of]])

;; ── check macro ──────────────────────────────────────────────────────
;; Chains (Option String) assertions: returns the first Some (failure),
;; short-circuiting. (check a b c) keeps the first failure, else the last value.

(defmacro check "Chain assertions, returning the first failure"
  ([x] x)
  ([x & rest]
    `(match ~x
       [(Some __f__) (Some __f__)
        None (check ~@rest)])))

;; ── Outcome ADT — a tally-able per-test result ───────────────────────

(deftype Outcome
  (Passed [:String name])
  (Failed [:String name :String why])
  (Panicked [:String name :String msg]))

;; ── Running a single discovered test ─────────────────────────────────
;; (Pair name thunk) -> Outcome, thunk bracketed by catch-runtime-error so a
;; panicking test becomes a value rather than aborting the whole run.

(defn run-one "Run one discovered (Pair name thunk), folding panic/pass/fail."
  [pair] :Outcome
  (match pair
    [(Pair name run)
       (match (catch-runtime-error run)
         [(Err msg) (Panicked name msg)
          (Ok inner)
            (match inner
              [None       (Passed name)
               (Some why) (Failed name why)])])]))

;; ── Discovery sugar (FIXME 0273 §2) — no-arg / module-name normalise to Vec ──
;; The canonical extern takes a (Vec String). `discover-here` normalises the
;; no-arg "current module" and module-name shapes to it; the body calls
;; `primitives/discover-tests` by FQ so the macro never recurses, and an empty
;; `[]` makes the extern fall back to the current module.
;;   (discover-here)            -> (primitives/discover-tests [])
;;   (discover-here "user.math")-> (primitives/discover-tests ["user.math"])
;;   (discover-here "a" "b")    -> (primitives/discover-tests ["a" "b"])

(defmacro discover-here "Discover tests in named modules (current module if none)."
  ([] `(primitives/discover-tests []))
  ([&mods] `(primitives/discover-tests [~@mods])))

;; ── The runner — ordinary map/filter over the pairs ──────────────────

(defn run-all "Run every eligible test in the current module."
  []
  (vec-map run-one (discover-tests [])))

(defn run-matching "Run only tests whose fully-qualified name contains substr."
  [:String substr]
  (vec-map run-one
    (vec-filter (fn [p] (ge-i64 (index-of (first p) substr) 0))
                (discover-tests []))))

;; ── Presenting outcomes ──────────────────────────────────────────────

(defn present-one "Render a single Outcome as a human-readable line."
  [:Outcome o] :String
  (match o
    [(Passed name)       (str-concat name " ... ok")
     (Failed name why)   (str-concat name (str-concat " ... FAIL: " why))
     (Panicked name msg) (str-concat name (str-concat " ... PANIC: " msg))]))

(defn report "Render a Vec of Outcomes as a multi-line report string."
  [outcomes] :String
  (report-loop outcomes (vec-len outcomes) 0 ""))

(defn- report-loop [outcomes :Int len :Int i :String acc] :String
  (if (ge-i64 i len) acc
    (report-loop outcomes len (add-i64 i 1)
      (str-concat acc (str-concat (present-one (vec-get outcomes i)) "\n")))))

;; ── Tallying outcomes ────────────────────────────────────────────────
;; A tally as a triple of counts (passes/fails/panics).

(deftype Tally [:Int passed :Int failed :Int panicked])

(defn- bump "Add one Outcome into a running Tally."
  [:Tally t :Outcome o] :Tally
  (match t
    [(Tally p f x)
       (match o
         [(Passed _)     (Tally (add-i64 p 1) f x)
          (Failed _ _)   (Tally p (add-i64 f 1) x)
          (Panicked _ _) (Tally p f (add-i64 x 1))])]))

(defn tally "Aggregate a Vec of Outcomes into pass/fail/panic counts."
  [outcomes] :Tally
  (tally-loop outcomes (vec-len outcomes) 0 (Tally 0 0 0)))

(defn- tally-loop [outcomes :Int len :Int i :Tally acc] :Tally
  (if (ge-i64 i len) acc
    (tally-loop outcomes len (add-i64 i 1) (bump acc (vec-get outcomes i)))))

(defn tally-line "Render a Tally as \"P passed, F failed, X panicked\"."
  [:Tally t] :String
  (match t
    [(Tally p f x)
       (str-concat (int-to-string p)
         (str-concat " passed, "
           (str-concat (int-to-string f)
             (str-concat " failed, "
               (str-concat (int-to-string x) " panicked")))))]))

(defn passed? "True iff a Tally has no failures and no panics."
  [:Tally t] :Bool
  (match t
    [(Tally _ f x) (if (eq-i64 f 0) (eq-i64 x 0) false)]))

;; ── Self-tests ───────────────────────────────────────────────────────
;; The `(mod- test)` body lives in the SEPARATE backing file
;; `testing/runner/test.cl` (module testing.runner.test) — authored as a file
;; rather than an inline body so the compiler's one-time inline-submodule
;; EXTRACTION (spec §8.2.5) cannot strip it. It super-imports the runner's
;; pure helpers and asserts with the in-language harness.

(mod- test)
