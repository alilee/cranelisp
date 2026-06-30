;; web_fanout/main.cl — the S96 C-fanout marquee fixture: a "server with no
;; `spawn`" whose per-connection handler is INLINED down to the raw `read-conn` /
;; `send-conn` poll leaves, so /int's bind-chain analysis sees a discarded,
;; value-local, ResourceSerial bind SUB-TREE over the freshly-accepted connection
;; token and INFERS the launch-and-continue fan-out (effect-concurrency.md §4.1
;; E1/E2/E3; FIXME 0470). There is NO `spawn`/`go`/`async` in the source — the
;; concurrency is written by nobody.
;;
;; Port: bound from `CRANELISP_PORT` (read platform-side by `bind-listener`) so the
;; e2e harness can use an ephemeral port (Gap G4 — no 8080 collision). Routes:
;;   /        →  200 "OK"          (health / liveness — proves the server lives)
;;   /slow    →  200 (slow handler) (the fan-out overlap witness)
;;   /fault   →  the handler FAULTS → `safe-handle`'s catch maps it to a 500 for
;;               THAT request, the server keeps serving (reactor.md §2.12 — the
;;               application-layer 500; the supervisor catch+drops the strand,
;;               the serve loop owns the 500 response).
;;
;; STATUS (S96, FIXME 0470 RESOLVED): the inline form below FIRES the inferred
;; launch and the launched web handler runs concurrently at runtime — the C-fanout
;; e2e rows in `tests/concurrency_fanout_web.rs` are GREEN. The 0470 wall was the
;; C4 `(slow-delay req)` step: a USER FN returning IO in an effect position is an
;; opaque footprint the launch-eligibility analysis (§4.1 E3) must refuse. Reshaped
;; to a DIRECT `(sleep (slow-ms req))` (a resource-free timer leaf, the §4.1 timer
;; refinement) the whole read→sleep→send handler sub-tree is launch-eligible and
;; detaches as one supervised strand per connection (read→sleep→send sequential
;; inside it). K concurrent /slow requests OVERLAP (≈1·D, the `sleep 100` parking
;; on the one reactor) instead of serialising (≈K·D).

(platform web)

(import [primitives [bind sleep catch-runtime-error Result Ok Err div-i64 int-to-string]])
(import [serve [listen accept]])
(import [platform.web [read-conn send-conn]])
(import [web [Connection Request Response]])

;; ── The pure router ───────────────────────────────────────────────────────
;; /fault deliberately faults (div-by-zero) — a catchable runtime error that
;; `safe-handle` maps to a 500. Other paths return 200.
(defn faulty-body [] (int-to-string (div-i64 1 0)))

(defn handle [req]
  (match req
    [(Request method path body)
       (if (= path "/fault")
         (Response 200 "text/html" (faulty-body))
         (Response 200 "text/html" "<html>OK</html>"))]))

;; The /slow route's deterministic parking delay (S96 C4 / 0470): the overlap
;; witness (`web_server_fans_out_concurrent_requests_overlap`) needs a REAL,
;; controllable handler delay so K concurrent /slow requests OVERLAP (≈1·D on the
;; one reactor) vs serialise (≈K·D). `slow-ms` is a PURE `(Fn [Request] Int)` —
;; 100 ms for `/slow`, 0 otherwise. The serve-loop calls `(sleep (slow-ms req))`
;; DIRECTLY, so the launch-eligibility analysis sees the `sleep` timer as a direct
;; platform/timer leaf in the discarded handler sub-tree (NOT an opaque user-fn IO
;; call — the C4 `slow-delay` user-fn-returning-IO shape was the 0470 wall: an
;; opaque footprint in an effect position is refused, §4.1 E3). `sleep` is the
;; resource-free timer leaf (the §4.1 timer refinement): it rides inside the
;; launched per-connection sub-tree so the fan-out fires; `(sleep 0)` for non-/slow
;; routes resolves immediately so the liveness checks stay fast.
(defn slow-ms [req]
  (match req
    [(Request method path body)
       (if (= path "/slow") 100 0)]))

;; ── The 500-safe handler (reactor.md §2.12 — application-layer 500) ───────────
;; Run the pure router under `catch-runtime-error`: a fault → a 500 for THAT
;; request, so a single bad request never wedges the connection / kills the loop.
(defn safe-handle [req]
  (match (catch-runtime-error (fn [] (handle req)))
    [(Ok resp)  resp
     (Err msg)  (Response 500 "text/html" "<html>500 internal error</html>")]))

;; ── The serve loop (CONCURRENT fan-out, inferred — NO `spawn`) ─────────────────
;; The per-connection handler is inlined to the raw poll leaves over the fresh
;; connection `token`; its result is DISCARDED (the `do`) and its footprint is
;; disjoint from the continuation's `listener` ⇒ /int infers the detached launch.
(defn serve-loop [listener]
  :(primitives/IO primitives/Int)
  (bind (accept listener)
    (fn [conn]
      (match conn
        [(Connection token capacity fd)
           (do
             ;; the discarded, launch-eligible per-connection handler sub-tree:
             ;; read → (sleep (slow-ms req)) → send. Every effect position is a
             ;; direct platform/timer leaf (read-conn/send-conn = ResourceSerial
             ;; poll over the fresh connection token; `sleep` = the resource-free
             ;; timer, §4.1 timer refinement), so /int infers the detached launch
             ;; and the `(sleep 100)` for /slow makes the overlap witness
             ;; deterministic. The handler launches as ONE strand (read→sleep→send
             ;; sequential inside); the `sleep` step is NOT independently detached.
             (bind (read-conn token capacity fd)
               (fn [req]
                 (bind (sleep (slow-ms req))
                   (fn [_] (send-conn token capacity fd (safe-handle req))))))
             ;; the continuation: accept the next connection (a fresh token)
             (serve-loop listener))]))))

;; ── Entry ──────────────────────────────────────────────────────────────────
;; The port arg is a fallback; `bind-listener` prefers `CRANELISP_PORT` when set.
(defn main []
  (bind (listen 8080 64)
    (fn [listener] (serve-loop listener))))
