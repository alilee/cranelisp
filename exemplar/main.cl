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
;;   POST /solve   →  parse → solve → solution-page  (or error-page)
;;   <anything>    →  not-found-page    (404)
;;
;; The router `handle :: (Fn [Request] Response)` is PURE — no IO, no socket —
;; so it is exercisable and testable without a server. The serve loop (Model A)
;; is the only IO: it owns the accept→handle→send→recur cycle in Cranelisp,
;; tail-recursive so the loop never grows the stack.
;;
;; Run it:
;;   CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
;;     cargo run -- --run exemplar/main.cl
;;
;; The exemplar is one of the two trees permitted to depend on stdlib
;; (root CLAUDE.md §Stdlib separation).

(platform web)

;; Idiomatic surface (S86 de-leak): trait operators bare via prelude; the
;; IO + string primitives imported by name.
(import [primitives [bind Pure]])

;; The web platform effects and the Request/Response ADTs it marshals.
(import [platform.web [listen accept send]])
(import [web [Request Response]])

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
(defn handle [req]
  (match req
    [(Request method path body)
       (if (= method "GET")
         (if (= path "/")
           (Response 200 "text/html" (form-page))
           (Response 404 "text/html" (not-found-page path)))
         (if (= method "POST")
           (if (= path "/solve")
             (solve-route body)
             (Response 404 "text/html" (not-found-page path)))
           (Response 405 "text/html"
             (error-page "Method not allowed"))))]))

;; ── The serve loop (Model A — explicit, single-threaded, TCO) ─────────────
;;
;; Cranelisp owns the loop: accept one request, run the pure handler, send the
;; response, recur. `serve-loop` is self-tail-recursive (the recursive call is
;; in tail position inside the bind continuation), so TCO keeps the stack flat
;; across unbounded requests.

;; The loop never terminates normally, so its result type is otherwise
;; unconstrained — `send` yields Int, so we pin the IO payload to Int.
(defn serve-loop []
  :(primitives/IO primitives/Int)
  (bind (accept)
    (fn [req]
      (bind (send (handle req))
        (fn [_] (serve-loop))))))

;; ── Headline web entry ────────────────────────────────────────────────────
;;
;; main : (Fn [] (IO _)). Bind the listener, then enter the serve loop.

(defn port [] 8080)

(defn main []
  (bind (listen (port))
    (fn [_] (serve-loop))))
