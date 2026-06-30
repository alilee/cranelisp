;; 32-concurrency-combinators.cl -- Explicit-control concurrency: race / select / timeout
;;
;; Cranelisp's concurrency model has TWO complementary halves (peers, not
;; primary-plus-footnote):
;;
;;   * The INFERRED half (throughput) -- examples 28 and 30. The compiler
;;     extracts parallelism from dataflow independence automatically. You
;;     write ordinary pure code with zero concurrency primitives and the
;;     results are provably identical to sequential execution. Concurrency
;;     "written by nobody."
;;
;;   * The CONTROL half (timing) -- THIS example. Everything that branches
;;     on completion *timing* -- races, deadlines, cancellation. Dataflow
;;     can say "B's value depends on A's value"; it can NEVER say "B's
;;     existence depends on A finishing first," or "give up after 200ms."
;;     That is irreducible, so it is a small set of in-language combinators.
;;
;; The combinators are ORDINARY TYPED FUNCTIONS, not special forms: each
;; takes IO value(s) and constructs a new IO value describing the
;; concurrent composition. Building the IO runs nothing; the composed
;; effect runs only when the IO is sequenced into the program and reaches
;; the trampoline (the single serializing interpreter).
;;
;;   sleep  :: (Fn [Int] (IO Int))         -- park d ms, then resume with 0
;;   race   :: (Fn [(IO a) (IO a)] (IO a)) -- first to complete wins; loser CANCELLED
;;   select :: (Fn [(Vec (IO a))] (IO a))  -- n-ary race over a Vec; all losers CANCELLED
;;
;; CANCELLATION is the load-bearing semantics underneath race/select: the
;; loser is not left running with its result discarded -- it is cancelled.
;; Its completion side-effect never occurs and its resources are released.
;; A race therefore completes in ~= the WINNER's wall-clock, not the loser's.
;;
;; TIMEOUT is not a primitive here. The standard library derives it as
;; `timeout d io === race io (sleep d)`, but examples MUST be free-standing
;; (no stdlib), so we express the timeout PATTERN INLINE: race the work
;; against a deadline branch built from `sleep`. If the work wins, we got a
;; result in time; if the deadline wins, the work timed out and is cancelled.
;;
;; Running:
;;   ./target/debug/cranelisp --run examples/32-concurrency-combinators.cl
;;
;; `sleep`/`race`/`select` are `primitives` builtins -- no platform DLL,
;; no environment variable. (Disable the INFERRED half with
;; CRANELISP_NO_LENIENT=1; it does not affect these explicit combinators.)

;; The combinators live in the `primitives` module alongside Pure/bind.
(import [primitives [Pure bind sleep race select]])


;; === Branch helpers ===
;;
;; Each `race`/`select` branch is an (IO Int). We define them as named
;; helpers (rather than inline at the call site) so each branch reads as
;; a self-contained unit of work -- the natural way to write real handlers.
;;
;; A "timeout sentinel" of 99 marks a deadline branch winning (= timed out),
;; distinguishable from any real result value.

;; Completes immediately -- a Pure is ready on the first trampoline turn.
(defn quick []
  (Pure 1))                                  ;; -> 1, instantly

;; "Fast work": parks 50 ms, then yields 111.
(defn fast-work []
  (bind (sleep 50) (fn [_] (Pure 111))))     ;; -> 111 after ~50ms

;; "Slow work": parks 300 ms, then yields 222.
(defn slow-work []
  (bind (sleep 300) (fn [_] (Pure 222))))    ;; -> 222 after ~300ms

;; "Work" for the timeout demos: parks 50 ms, then yields a real result 7.
(defn io-quick []
  (bind (sleep 50) (fn [_] (Pure 7))))       ;; -> 7 after ~50ms

;; "Slow work" for the timeout demos: parks 300 ms, then yields 7.
(defn io-slow []
  (bind (sleep 300) (fn [_] (Pure 7))))      ;; -> 7 after ~300ms

;; A LONG deadline (300 ms) -- the work usually beats it. Yields the
;; timeout sentinel 99 if it ever wins.
(defn deadline-long []
  (bind (sleep 300) (fn [_] (Pure 99))))     ;; -> 99 after ~300ms

;; A SHORT deadline (50 ms) -- slow work loses to it. Yields sentinel 99.
(defn deadline-short []
  (bind (sleep 50) (fn [_] (Pure 99))))      ;; -> 99 after ~50ms


;; === Test 1: race -- an immediately-ready branch always wins ===
;;
;; `quick` is ready on the first turn; `slow-work` needs 300 ms. By the
;; time the runtime observes `quick`, `slow-work` has not completed -- so
;; `quick` wins deterministically and `slow-work` is CANCELLED (its 300 ms
;; park never finishes; its value 222 is never produced).

(defn test-race-immediate-wins []
  (bind (race (quick) (slow-work))
    (fn [r] (Pure (if (eq-i64 r 1) 1 0)))))  ;; winner = quick (1) -> pass 1


;; === Test 2: race -- the faster of two delayed branches wins ===
;;
;; `fast-work` (50 ms) completes before `slow-work` (300 ms), so its value
;; 111 is returned. `slow-work` is cancelled -- the whole race completes in
;; ~50 ms, NOT ~300 ms. (A race that ran both to completion would be a Par.)

(defn test-race-faster-wins []
  (bind (race (fast-work) (slow-work))
    (fn [r] (Pure (if (eq-i64 r 111) 1 0))))) ;; winner = fast-work (111) -> pass 1


;; === Test 3: select -- n-ary race over a Vec of branches ===
;;
;; `select` generalises `race` to a Vec: it runs every branch and completes
;; with the first to finish; all other branches are cancelled. Here the
;; middle branch (`fast-work`, 50 ms) wins against two `slow-work` (300 ms)
;; branches. `select [a b]` is observationally equivalent to `race a b`.
;; (`select` takes a Vec literal `[...]`, never a List; the empty `select []`
;; never completes -- a program must not rely on it.)

(defn test-select-first-wins []
  (bind (select [(slow-work) (fast-work) (slow-work)])
    (fn [r] (Pure (if (eq-i64 r 111) 1 0))))) ;; winner = fast-work (111) -> pass 1


;; === Test 4: timeout PATTERN -- work completes before the deadline ===
;;
;; Inline timeout = race the work against a deadline branch. `io-quick`
;; (50 ms, result 7) beats `deadline-long` (300 ms), so we get the real
;; result 7 -- NOT the sentinel 99. The deadline branch is cancelled.

(defn test-timeout-completes []
  (bind (race (io-quick) (deadline-long))
    (fn [r] (Pure (if (eq-i64 r 7) 1 0)))))   ;; work won -> result 7 -> pass 1


;; === Test 5: timeout PATTERN -- the deadline fires, work is cancelled ===
;;
;; `io-slow` (300 ms) loses to `deadline-short` (50 ms), so the race
;; completes with the timeout sentinel 99 in ~50 ms. The slow work is
;; CANCELLED -- its 300 ms park never finishes and its result 7 never
;; appears. This is the per-request-timeout pattern: bound the work in time
;; and stop it cleanly when it overruns.

(defn test-timeout-fires []
  (bind (race (io-slow) (deadline-short))
    (fn [r] (Pure (if (eq-i64 r 99) 1 0)))))  ;; deadline won -> sentinel 99 -> pass 1


;; === Test 6: sleep -- the timer leaf the rest are built on ===
;;
;; `(sleep d)` parks the strand for d ms then resumes with 0. The bind
;; continuation runs AFTER the timer fires, proving the park-then-resume.

(defn test-sleep-resumes []
  (bind (sleep 50) (fn [_] (Pure 42))))       ;; continuation ran -> 42, then check below


;; --- Verify all results ---
;;
;; Each sub-test contributes 1 to the pass count when its outcome is
;; correct. Six sub-tests all pass -> main returns 6 -> exit code 6.
;; A regression in any combinator drops the count below 6.
;;
;; Wall-clock: every race cancels its loser, so each race completes in
;; ~= the winner's delay (~50 ms or instant), not the loser's 300 ms.
;; Total runtime is a few hundred ms, not seconds.

(defn main []
  (bind (test-race-immediate-wins) (fn [a]
  (bind (test-race-faster-wins) (fn [b]
  (bind (test-select-first-wins) (fn [c]
  (bind (test-timeout-completes) (fn [d]
  (bind (test-timeout-fires) (fn [e]
  (bind (test-sleep-resumes) (fn [r6]
    (Pure (add-i64 a (add-i64 b (add-i64 c (add-i64 d (add-i64 e (if (eq-i64 r6 42) 1 0)))))))
  )))))))))))))
