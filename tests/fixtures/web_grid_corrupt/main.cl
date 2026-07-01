;; web_grid_corrupt/main.cl — the S97 launched-strand heap-corruption repro
;; fixture (bug #2 — DISTINCT from the now-fixed single-threaded inline-temporary
;; `emit_vec_drop_if_temporary` defect).
;;
;; A minimal "server with no `spawn`" whose per-connection handler is launched
;; (launch-and-continue: the discarded read→sleep→send sub-tree over the fresh
;; `conn`; the `serve-loop` recursion is the continuation). Inside that LAUNCHED
;; strand the handler:
;;   1. builds an ADT-wrapping-Vec grid `g` (`Grid` wraps a `(Vec Cell)`),
;;   2. derives a second grid `s = (churn g …)` via `set-cell` (user-fn `assoc`
;;      over `vec-set`) — so `g` AND `s` are BOTH live simultaneously,
;;   3. renders BOTH grids' cells (user-fn `get`/`cell-at` over `vec-get`)
;;      interleaved with heavy string allocation, and
;;   4. `send-conn`s the rendered page.
;;
;; This is the free-standing reduction of the exemplar Sudoku `web` server's
;; `(solution-page solution g)` step (html.cl `solution-cell` reads BOTH the
;; original `g` and the solved grid). It reproduces `exemplar/main.cl`'s
;; `free(): chunks in smallbin corrupted` abort DETERMINISTICALLY (10/10, both
;; default AND `CRANELISP_NO_LENIENT=1`), driven by a read-to-EOF HTTP client.
;;
;; Grid vec access goes through the thin USER-FN wrappers `get`/`assoc` (exactly
;; as stdlib `collections.vec/get`/`assoc` are thin wrappers over `vec-get`/
;; `vec-set`) — the extra call frame is the borrowed-Var-param RC path
;; (`ring2-rc.md §5.5` borrowed_vars / `emit_capture_return_inc`), which LEAKS
;; but does NOT corrupt single-threaded, and CORRUPTS under the launched strand.
;;
;; Free-standing: primitives + the `web` platform leaves only, ZERO stdlib.

(platform web)
(import [primitives [bind sleep vec-get vec-set vec-push int-to-string str-concat sub-i64 le-i64 Int]])
(import [serve [listen accept]])
(import [platform.web [read-conn send-conn]])
(import [web [Request Response]])

;; ── An ADT wrapping a (Vec Cell) — the Sudoku Grid shape ──────────────────
(deftype Cell (Given [:Int v]) (Solved [:Int v]))
(deftype Grid [cells])

;; Thin user-fn wrappers = stdlib collections.vec get/assoc/conj (Var-param
;; borrowed-vec RC path — the load-bearing difference from the direct-primitive
;; deterministic repro in regression.rs).
(defn get [v :Int i] (vec-get v i))
(defn assoc [v :Int i x] (vec-set v i x))
(defn conj [v x] (vec-push v x))

(defn cval [c] (match c [(Given x) x (Solved x) x]))
(defn cell-at [g idx] (match g [(Grid cells) (get cells idx)]))
(defn set-cell [g idx c] (match g [(Grid cells) (Grid (assoc cells idx c))]))
(defn build [v i] (if (le-i64 i 0) v (build (conj v (Given i)) (sub-i64 i 1))))

;; Derive a second grid from g via set-cell (assoc) churn — g and the result are
;; BOTH live during the render below (the `(solution-page solution g)` shape).
(defn churn [g i] (if (le-i64 i 0) g (churn (set-cell g (sub-i64 i 1) (Solved i)) (sub-i64 i 1))))

(defn td [cls d] (str-concat (str-concat "<td class=\"" cls) (str-concat "\">" (str-concat d "</td>"))))

;; solution-cell shape: read BOTH orig + solved grids, match orig, td-wrap.
(defn scell [orig sol idx]
  (let [oc (cell-at orig idx)
        sc (cell-at sol idx)
        digit (int-to-string (cval sc))]
    (match oc [(Given _) (td "given" digit) _ (td "solved" digit)])))

(defn render [orig sol i acc]
  (if (le-i64 i 0) acc
    (render orig sol (sub-i64 i 1) (str-concat acc (scell orig sol (sub-i64 i 1))))))

;; PURE — computed as the argument to the `send-conn` leaf inside the strand.
(defn make-resp [req]
  (let [g (Grid (build [] 81))
        s (churn g 81)]
    (Response 200 "text/html" (str-concat "<title>Solution</title>" (render g s 81 "")))))

;; ── The launched serve loop (inferred launch-and-continue — NO `spawn`) ──────
(defn serve-loop [listener]
  :(primitives/IO primitives/Int)
  (bind (accept listener)
    (fn [conn]
      (bind
        ;; the discarded, launch-eligible per-connection handler sub-tree:
        (bind (read-conn conn)
          (fn [req] (bind (sleep 0) (fn [_] (send-conn conn (make-resp req))))))
        ;; the continuation: accept the next connection.
        (fn [_] (serve-loop listener))))))

(defn main [] (bind (listen 8080 64) (fn [listener] (serve-loop listener))))
