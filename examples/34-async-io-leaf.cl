;; 34-async-io-leaf.cl -- A poll-shape platform IO leaf: suspend on the reactor
;;
;; Examples 21, 22 and 24 used BLOCKING platform effects (`print`, `read-line`): the
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
;; Executing a leaf suspends until its timer is ready; bind then receives
;; the resumed value. These checks observe results, not thread count or time.
;; Even equal delays are sequential below: the second action is constructed
;; inside the first continuation, after the first action has completed.
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
(import [primitives [pure bind]])


;; === Test 1: a single poll-shape leaf resumes with its result ===
;;
;; `(async-read 4)` suspends ~4 ms on the reactor, then resumes producing 4.
;; The bind continuation observes the resumed value.

(defn check-single-read []
  (bind (async-read 4)
    (fn [r] (pure (if (eq-i64 r 4) 1 0)))))            ;; resumed with 4 -> pass 1


;; === Test 2: the continuation runs AFTER the leaf resumes ===
;;
;; If the leaf really suspended and resumed with a value (not a placeholder),
;; then `(add-i64 r 1)` in the continuation sees 4 and yields 5. A continuation
;; that ran before the resume would see garbage.

(defn check-continuation-after-resume []
  (bind (async-read 4)
    (fn [r] (pure (if (eq-i64 (add-i64 r 1) 5) 1 0))))) ;; continuation saw 4 -> pass 1


;; === Test 3: a data DEPENDENCY threaded through two suspensions ===
;;
;; The second read's delay depends on the first read's result, so the two
;; leaves MUST run in order: read a = 3, then read b = a+1 = 4. Their sum is 7.
;; Two suspend/resume cycles, sequenced by the dataflow.

(defn check-dependent-reads []
  (bind (async-read 3)
    (fn [a]
      (bind (async-read (add-i64 a 1))
        (fn [b] (pure (if (eq-i64 (add-i64 a b) 7) 1 0))))))) ;; 3 + 4 -> pass 1


;; === Test 4: equal delays still sequence through bind ===
;;
;; The delays need no shared input, but bind imposes execution order.
;; Two successive resumptions produce 5 and 5; their sum is 10.

(defn check-sequential-reads []
  (bind (async-read 5)
    (fn [a]
      (bind (async-read 5)
        (fn [b] (pure (if (eq-i64 (add-i64 a b) 10) 1 0))))))) ;; 5 + 5 -> pass 1


;; --- Verify all results ---
;;
;; Four sub-tests, each contributing 1 when correct -> main returns 4 -> exit 4.
;; The count checks resumed values and their use by continuations.
;; It makes no claim about overlap or elapsed time.

(defn main []
  (bind (check-single-read) (fn [a]
  (bind (check-continuation-after-resume) (fn [b]
  (bind (check-dependent-reads) (fn [c]
  (bind (check-sequential-reads) (fn [d]
    (pure (add-i64 a (add-i64 b (add-i64 c d)))))))))))))
