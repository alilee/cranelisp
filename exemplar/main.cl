;; main.cl — Sudoku Solver: the web entry point.
;;
;; Wires the Sudoku core to the `web` platform (exemplar/platforms/web/).
;;
;;   GET  /        →  form-page         (9×9 puzzle-entry grid)
;;   GET  /slow    →  ok-page after a fixed delay (the fan-out demonstration)
;;   POST /solve   →  parse → solve → solution-page  (or error-page)
;;   <anything>    →  not-found-page    (404)
;;
;; Run with `--run exemplar/main.cl`, or `--link` it and run the binary; either
;; serves until killed. The router `handle :: (Fn [Request] Response)` performs
;; no IO: its result type contains none.
;;
;; Concurrency is inferred, not written: the serve loop discards a
;; per-connection sub-tree of direct leaves (`read-conn` → `sleep` →
;; `send-conn`) whose footprint is disjoint from `listener`, so each connection
;; runs on its own supervised strand. Keep every effect position in that
;; sub-tree a direct leaf. A user function returning IO there is opaque to the
;; analysis and silently serialises the server; helpers such as `slow-ms` and
;; `handle`, whose result types contain no `IO`, compute leaf arguments only (plan-exemplar.md, "Web server").
;;
;; A runtime panic ends the server, so `handle` must not panic on any request.
;; Every value a request supplies reaches only total operations; bad input
;; renders the error page (plan-exemplar.md, "Web server").

(platform web)

(import [primitives [bind sleep]])

;; `read-conn`/`send-conn` come straight from `platform.web` so they stay direct
;; leaves; `listen`/`accept` are wrappers in `serve.cl` (see web.cl for why).
(import [serve [listen accept]])
(import [platform.web [read-conn send-conn]])
(import [web [Request Response]])

;; The Sudoku core, shared with the stdio entries.
(import [form   [parse-form-body]])
(import [grid   [make-grid Success Unsolvable]])
(import [solver [solve]])
(import [html   [form-page solution-page error-page not-found-page]])

;; ── The router ───────────────────────────────────────────────────────────

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

;; Map method and path to a Response. GET /slow answers a plain page; its
;; delay comes from `slow-ms` at the serve loop's `sleep` leaf, not from here.
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

;; The delay before responding: 100 ms for `/slow` (the fan-out witness), 0 for
;; every other route. It computes the argument of the serve loop's `sleep` leaf
;; and must not itself return IO.
(defn slow-ms [req]
  (match req
    [(Request method path body)
       (if (= path "/slow") 100 0)]))

;; ── The serve loop (CONCURRENT fan-out, inferred — NO `spawn`) ─────────────
;;
;; Accept one connection, launch its discarded handler sub-tree (read → sleep →
;; send) and continue (design/arch/effect-concurrency.md §4.1). Each iteration
;; binds a fresh `conn`, so in-flight handlers overlap. The recursive call is the
;; continuation and is a tail call, so the stack stays flat; the loop never
;; returns, and its IO payload is Int because `send-conn` yields Int.
(defn serve-loop [listener]
  :(primitives/IO primitives/Int)
  (bind (accept listener)
    (fn [conn]
      (do
        ;; the discarded per-connection handler: direct leaves only, launched as
        ;; one supervised strand.
        (bind (read-conn conn)
          (fn [req]
            (bind (sleep (slow-ms req))
              (fn [_] (send-conn conn (handle req))))))
        ;; the continuation: accept the next connection (a fresh opaque handle)
        (serve-loop listener)))))

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
