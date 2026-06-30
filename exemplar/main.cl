;; main.cl — Sudoku Solver: the WEB entry point.
;;
;; This wires the pure Sudoku core to the `web` HTTP platform DLL
;; (exemplar/platforms/web/, Sprint 86 Wave E). It is the browser-facing
;; counterpart to the stdio showcase in `user.cl` — both coexist:
;;
;;   web   :  --link exemplar/main.cl  (then run the binary; it serves)
;;            --run  exemplar/main.cl  (serves until killed)
;;   stdio :  --run  exemplar/user.cl  (one-shot solve-and-print)
;;
;; The HTTP roundtrip:
;;
;;   GET  /        →  form-page         (9×9 puzzle-entry grid)
;;   GET  /slow    →  ok-page (after a deterministic delay — the fan-out demo)
;;   POST /solve   →  parse → solve → solution-page  (or error-page)
;;   <anything>    →  not-found-page    (404)
;;
;; The router `handle :: (Fn [Request] Response)` is PURE — no IO, no socket —
;; so it is exercisable and testable without a server.
;;
;; ── The marquee: a concurrent server with NO `spawn` (S96, FIXME 0470/0472) ──
;;
;; The serve loop INFERS launch-and-continue concurrency. The per-connection
;; handler is INLINED as a sub-tree of DIRECT poll/timer leaves
;; (`read-conn` → `sleep` → `send-conn`); its result is DISCARDED (the `do`)
;; and its footprint is disjoint from the continuation's `listener`, so /int's
;; bind-chain analysis (effect-concurrency.md §4.1 E1/E2/E3) infers a detached
;; launch — one supervised strand per connection. There is NO `spawn`/`go`/
;; `async` in the source: the concurrency is written by nobody. K concurrent
;; /slow requests OVERLAP (≈1·D on the one reactor) instead of serialising
;; (≈K·D), witnessed by `tests/exemplar_web.rs`.
;;
;; THE DIRECT-LEAF DISCIPLINE (why this fires where the earlier serial loop did
;; not): every EFFECT POSITION in the handler sub-tree must be a DIRECT
;; launchable leaf — `read-conn`/`send-conn` (ResourceSerial poll leaves over the
;; fresh connection token) or `sleep` (the resource-free timer leaf, §4.1 timer
;; refinement). A USER FUNCTION that RETURNS IO in an effect position (the old
;; `handle-conn` wrapper, or a `(slow-delay req)` returning `(IO _)`) is an
;; OPAQUE footprint the eligibility analysis (§4.1 E3) must refuse → the launch
;; is suppressed and the server silently serialises. So pure helpers compute the
;; leaves' ARGUMENTS only: `slow-ms : Request -> Int` (the delay) and
;; `safe-handle : Request -> Response` (the 500-safe pure router) are values fed
;; to the direct `sleep`/`send-conn` leaves — never themselves placed in an
;; effect position.

(platform web)

;; Idiomatic surface (S86 de-leak): trait operators bare via prelude; the
;; IO + timer + catch primitives imported by name.
(import [primitives [bind sleep catch-runtime-error Result Ok Err]])

;; The web platform connection lifecycle. `listen`/`accept` stay behind the
;; serve.cl destructuring wrappers (they supply the poll leading (token,
;; capacity) pair); the per-connection `read-conn`/`send-conn` poll leaves are
;; imported RAW from `platform.web` so the serve loop can inline them down to
;; direct leaves — the discipline the inferred launch requires (see header).
;; The wrappers live in `serve` not `web` to avoid the platform-load pre-resolve
;; cycle (see web.cl/serve.cl).
(import [serve [listen accept]])
(import [platform.web [read-conn send-conn]])
(import [web [Connection Request Response]])

;; The pure Sudoku core (shared verbatim with the stdio showcase).
(import [form   [parse-form-body]])
(import [grid   [make-grid SolveResult Success Unsolvable]])
(import [solver [solve]])
(import [html   [form-page solution-page error-page not-found-page]])

;; ── The pure router ──────────────────────────────────────────────────────
;;
;; `handle :: (Fn [Request] Response)` — pure. Maps method + path to a
;; Response. No IO; trivially testable; safe to call from any thread.

;; POST /solve: parse the URL-encoded body into a puzzle string, build the
;; grid, solve, and render. A bad puzzle string or an unsolvable puzzle both
;; render an error page (200 text/html — the request itself was well-formed).
(defn solve-route [body]
  (let [puzzle (parse-form-body body)]
    (match (make-grid puzzle)
      [None
         (Response 200 "text/html" (error-page "Invalid puzzle input"))
       (Some g)
         (match (solve g)
           [(Success solution)
              (Response 200 "text/html" (solution-page solution g))
            Unsolvable
              (Response 200 "text/html" (error-page "No solution exists"))])])))

;; The route table. Match on (method, path) via nested match on the Request
;; fields (no accessor fns — fields come out of the constructor pattern).
;; GET /slow is the fan-out demonstration endpoint: a plain 200 page whose
;; concurrency-witness delay is supplied by `slow-ms` at the serve-loop's
;; direct `sleep` leaf (NOT here — `handle` stays pure and instantaneous).
(defn handle [req]
  (match req
    [(Request method path body)
       (if (= method "GET")
         (if (= path "/")
           (Response 200 "text/html" (form-page))
           (if (= path "/slow")
             (Response 200 "text/html" "<html><body>OK</body></html>")
             (Response 404 "text/html" (not-found-page path))))
         (if (= method "POST")
           (if (= path "/solve")
             (solve-route body)
             (Response 404 "text/html" (not-found-page path)))
           (Response 405 "text/html"
             (error-page "Method not allowed"))))]))

;; slow-ms : (Fn [Request] Int) — PURE. The per-request parking delay, keyed on
;; path: 100 ms for `/slow` (the fan-out overlap witness), 0 for every real
;; route so the Sudoku pages stay instantaneous. This is a pure helper that
;; computes the ARGUMENT to the serve loop's direct `(sleep …)` leaf — it does
;; NOT itself sit in an effect position (that would be the opaque-footprint trap
;; that suppresses the launch, §4.1 E3).
(defn slow-ms [req]
  (match req
    [(Request method path body)
       (if (= path "/slow") 100 0)]))

;; safe-handle : (Fn [Request] Response) — PURE. The 500-safe router
;; (reactor.md §2.12 — the application-layer 500). Run the pure router under
;; `catch-runtime-error`: a fault → a 500 page for THAT request, so a single bad
;; request never wedges the connection / kills the serve loop. The result is a
;; plain `Response` VALUE fed to the `send-conn` leaf — pure, so it does not
;; suppress the inferred launch.
(defn safe-handle [req]
  (match (catch-runtime-error (fn [] (handle req)))
    [(Ok resp)  resp
     (Err msg)  (Response 500 "text/html" (error-page "Internal server error"))]))

;; ── The serve loop (CONCURRENT fan-out, inferred — NO `spawn`) ─────────────
;;
;; accept one connection, then LAUNCH-AND-CONTINUE: the per-connection handler
;; sub-tree (read → sleep → send) is inlined to direct leaves and DISCARDED (the
;; `do`), its footprint disjoint from the continuation's `listener`, so /int
;; infers the detached launch (effect-concurrency.md §4.1 E1/E2/E3). Each
;; iteration binds a FRESH `conn` (distinct token), so in-flight handlers ride
;; distinct connection tokens and overlap on the one reactor. The recursive
;; `serve-loop` call is the continuation: accept the next connection immediately
;; rather than waiting for this one to finish. TCO keeps the stack flat across
;; unbounded connections; the loop never terminates normally, so its IO payload
;; is pinned to Int (`send-conn` yields Int).
(defn serve-loop [listener]
  :(primitives/IO primitives/Int)
  (bind (accept listener)
    (fn [conn]
      (match conn
        [(Connection token capacity fd)
           (do
             ;; the discarded, launch-eligible per-connection handler sub-tree.
             ;; Every effect position is a DIRECT leaf: read-conn/send-conn
             ;; (ResourceSerial poll over the fresh connection token) + `sleep`
             ;; (the resource-free timer leaf). The pure `slow-ms`/`safe-handle`
             ;; only compute leaf arguments. So the whole read→sleep→send handler
             ;; launches as ONE supervised strand per connection.
             (bind (read-conn token capacity fd)
               (fn [req]
                 (bind (sleep (slow-ms req))
                   (fn [_] (send-conn token capacity fd (safe-handle req))))))
             ;; the continuation: accept the next connection (a fresh token)
             (serve-loop listener))]))))

;; ── Headline web entry ────────────────────────────────────────────────────
;;
;; main : (Fn [] (IO _)). Bind the listener (pool ceiling N), then enter the
;; serve loop. N is the in-flight-CONNECTION-COUNT ceiling for the fan-out.
;; The listening port is `(port)` unless `CRANELISP_PORT` overrides it
;; (platform-side, in `bind-listener`) — the e2e harness uses an ephemeral port.

(defn port [] 8080)
(defn pool-size [] 64)

(defn main []
  (bind (listen (port) (pool-size))
    (fn [listener] (serve-loop listener))))
