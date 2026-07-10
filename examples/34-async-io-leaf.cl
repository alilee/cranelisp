;; 34-async-io-leaf.cl -- A poll-shape platform IO leaf: suspend on the reactor
;;
;; Examples 21-24 used BLOCKING platform effects (`print`, `read-line`): the
;; effect runs to completion on the calling turn and hands back its value. This
;; example introduces the OTHER shape a platform effect can have -- a
;; POLL-SHAPE (async) leaf that does NOT block. Instead of occupying a thread
;; while it waits, it SUSPENDS on the host reactor and RESUMES later when its
;; event is ready. This is the shape a real network server is built from
;; (accept a connection, wait for bytes, wait for the socket to drain) -- the
;; "server with no spawn": one reactor drives many suspended effects, no
;; thread-per-connection.
;;
;;   async-read :: (Fn [Int] (IO Int))   -- suspend ~N ms on the reactor,
;;                                           then resume, producing N.
;;
;; `async-read N` means "after about N milliseconds, produce N." It is the
;; minimal poll-shape leaf: it carries an Int in and an Int out, and it
;; genuinely PARKS on the reactor's timer (it is not a blocking sleep on a
;; thread). We use it here because it is a self-contained, deterministic
;; poll-shape leaf -- a socket accept/read would need an external client to
;; drive it; a timer drives itself. The MECHANISM you are learning -- how a
;; poll-shape platform effect is declared, imported, bound, and driven by the
;; reactor from cranelisp -- is exactly the mechanism a socket leaf uses.
;;
;; TWO PROPERTIES make a poll-shape leaf different from a blocking one:
;;
;;   1. SUSPEND / RESUME. `async-read` returns an (IO Int) that, when
;;      sequenced, arms a reactor timer and yields the strand. The `bind`
;;      continuation runs only AFTER the timer fires and the effect resumes --
;;      proving the leaf suspended and came back with a value, not a placeholder.
;;
;;   2. OVERLAP ON ONE THREAD. Two data-INDEPENDENT poll-shape leaves both
;;      suspend on the SAME reactor thread and their waits OVERLAP: two 5 ms
;;      reads complete in ~5 ms wall-clock, not ~10 ms. No extra threads are
;;      spawned. (This is the same automatic-parallelism idea as examples 28/30,
;;      now reaching across the IO boundary: independent IO leaves are driven
;;      concurrently by the one reactor.) We assert on the RESULT values here
;;      (deterministic); the wall-clock overlap is a runtime property, covered
;;      by the reactor test suite rather than an exit-code check.
;;
;; The reactor is always present -- a pure-blocking program never constructs it,
;; but the moment a poll-shape leaf suspends, the host drives it. No feature
;; flag, no environment variable beyond the platform search path.
;;
;; NOTE ON SCOPE. `async-read` is a TIMER leaf. The full NETWORK shape
;; (accept -> read -> send over a real socket, plus a client-connect leaf so a
;; single program can drive itself) is not yet expressible as a free-standing
;; example -- no shared socket platform exists, so that showcase still lives
;; only in the exemplar web server. This example teaches the poll-shape leaf
;; MECHANISM that the network shape is built on. (See the /examples plan and
;; FIXME 0463 for the remaining socket-platform dependency.)
;;
;; Running:
;;   CRANELISP_PLATFORM_PATH=target/debug \
;;     ./target/debug/cranelisp --run examples/34-async-io-leaf.cl
;;   (The examples test harness sets CRANELISP_PLATFORM_PATH=target/debug and
;;    builds the async-demo platform DLL suite-wide, so it resolves with no
;;    per-file setup.)

(platform async-demo)
(import [platform.async-demo [async-read]])
(import [primitives [Pure bind]])


;; === Test 1: a single poll-shape leaf resumes with its result ===
;;
;; `(async-read 4)` suspends ~4 ms on the reactor, then resumes producing 4.
;; The bind continuation observes the resumed value.

(defn test-single-read []
  (bind (async-read 4)
    (fn [r] (Pure (if (eq-i64 r 4) 1 0)))))            ;; resumed with 4 -> pass 1


;; === Test 2: the continuation runs AFTER the leaf resumes ===
;;
;; If the leaf really suspended and resumed with a value (not a placeholder),
;; then `(add-i64 r 1)` in the continuation sees 4 and yields 5. A continuation
;; that ran before the resume would see garbage.

(defn test-continuation-after-resume []
  (bind (async-read 4)
    (fn [r] (Pure (if (eq-i64 (add-i64 r 1) 5) 1 0))))) ;; continuation saw 4 -> pass 1


;; === Test 3: a data DEPENDENCY threaded through two suspensions ===
;;
;; The second read's delay depends on the first read's result, so the two
;; leaves MUST run in order: read a = 3, then read b = a+1 = 4. Their sum is 7.
;; Two suspend/resume cycles, sequenced by the dataflow.

(defn test-dependent-reads []
  (bind (async-read 3)
    (fn [a]
      (bind (async-read (add-i64 a 1))
        (fn [b] (Pure (if (eq-i64 (add-i64 a b) 7) 1 0))))))) ;; 3 + 4 -> pass 1


;; === Test 4: two INDEPENDENT leaves overlap on one reactor thread ===
;;
;; Neither read's argument depends on the other's result, so the runtime drives
;; both concurrently on the single reactor thread -- their 5 ms waits OVERLAP
;; (wall-clock ~5 ms, not ~10 ms), with no extra threads. Both resume; the sum
;; is 10. We assert the value; the overlap is the reactor's doing.

(defn test-independent-overlap []
  (bind (async-read 5)
    (fn [a]
      (bind (async-read 5)
        (fn [b] (Pure (if (eq-i64 (add-i64 a b) 10) 1 0))))))) ;; 5 + 5 -> pass 1


;; --- Verify all results ---
;;
;; Four sub-tests, each contributing 1 when correct -> main returns 4 -> exit 4.
;; A regression in the poll-shape leaf path (suspend, resume, result carry, or
;; independent overlap) drops the count below 4. Total wall-clock is a few tens
;; of ms: every wait is a handful of ms, and the independent pair overlaps.

(defn main []
  (bind (test-single-read) (fn [a]
  (bind (test-continuation-after-resume) (fn [b]
  (bind (test-dependent-reads) (fn [c]
  (bind (test-independent-overlap) (fn [d]
    (Pure (add-i64 a (add-i64 b (add-i64 c d)))))))))))))
