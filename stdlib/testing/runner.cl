;; testing/runner.cl — In-language test runner over discovered test pairs
;;
;; An ordinary map/filter runner over the fn-value pairs `discover-tests`
;; returns (design/arch/test-discovery.md §4.3/§5/§6). The callables are
;; late-bound, so `vec-map` over a fresh `(discover-tests)` call always sees
;; the current test set.
;;
;;   discover-tests :: (Fn [(Vec String)] (Vec (Pair String (Fn [] (Option String)))))
;;
;; A test is a zero-arg fn named `test-*` of type `(Fn [] (Option String))`:
;; None is a pass, (Some why) an assertion failure.
;;
;; NO PANIC ISOLATION. Every test runs in the calling process, so a panicking
;; test ends that process and the tests after it do not run
;; (spec/12-runtime.md §12.7.4). Isolation is the `cranelisp --test`
;; supervisor's, which restarts its child after a panic
;; (design/arch/s123-panics-and-environment.md §1.5).
;;
;; REPL ONLY, WHOLE MODULE. `run-all` and `run-matching` reference
;; `discover-tests`, and importing any name from this module (or from
;; `testing`) compiles them. `--run`, `--link`, `--test` and every test child
;; therefore refuse the program before it runs, even when it imports only a
;; pure helper such as `run-one` and never calls discovery (REPL spec §16.6).
;;
;; Spec: design/arch/test-discovery.md §4.3/§5/§6, plan-stdlib.md §3.3

(import [prelude []])

(import [primitives [discover-tests
                     Int Bool String Pair Option Some None
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
  (Passed [:String passed-name])
  (Failed [:String failed-name :String why]))

;; ── Running a single discovered test ─────────────────────────────────

(defn run-one "Run one discovered (Pair name thunk) in this process, folding pass/fail."
  [pair] :Outcome
  (match pair
    [(Pair name run)
       (match (run)
         [None       (Passed name)
          (Some why) (Failed name why)])]))

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
     (Failed name why)   (str-concat name (str-concat " ... FAIL: " why))]))

(defn report "Render a Vec of Outcomes as a multi-line report string."
  [outcomes] :String
  (report-loop outcomes (vec-len outcomes) 0 ""))

(defn- report-loop [outcomes :Int len :Int i :String acc] :String
  (if (ge-i64 i len) acc
    (report-loop outcomes len (add-i64 i 1)
      (str-concat acc (str-concat (present-one (vec-get outcomes i)) "\n")))))

;; ── Tallying outcomes ────────────────────────────────────────────────

(deftype Tally [:Int passed :Int failed])

(defn- bump "Add one Outcome into a running Tally."
  [:Tally t :Outcome o] :Tally
  (match t
    [(Tally p f)
       (match o
         [(Passed _)   (Tally (add-i64 p 1) f)
          (Failed _ _) (Tally p (add-i64 f 1))])]))

(defn tally "Aggregate a Vec of Outcomes into pass/fail counts."
  [outcomes] :Tally
  (tally-loop outcomes (vec-len outcomes) 0 (Tally 0 0)))

(defn- tally-loop [outcomes :Int len :Int i :Tally acc] :Tally
  (if (ge-i64 i len) acc
    (tally-loop outcomes len (add-i64 i 1) (bump acc (vec-get outcomes i)))))

(defn tally-line "Render a Tally as \"P passed, F failed\"."
  [:Tally t] :String
  (match t
    [(Tally p f)
       (str-concat (int-to-string p)
         (str-concat " passed, "
           (str-concat (int-to-string f) " failed")))]))

(defn passed? "True iff a Tally has no failures."
  [:Tally t] :Bool
  (match t
    [(Tally _ f) (eq-i64 f 0)]))

;; ── Self-tests ───────────────────────────────────────────────────────
;; Backing file `testing/runner/test.cl` (module testing.runner.test).

(mod- test)
