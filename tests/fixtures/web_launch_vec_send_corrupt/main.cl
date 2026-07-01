;; web_launch_vec_send_corrupt/main.cl — the SMALLER reduction of exemplar-web
;; bug #2 (FIXME 0486): a launched per-connection handler that renders TWO live
;; `(Vec Int)`s via the borrowed-Var `get`/`assoc` wrappers, then `send-conn`s the
;; page. Drops the `Cell` / `Grid` ADT wrappers of the larger sibling
;; `web_grid_corrupt/main.cl` — smaller CLIF for the /backend keep-alive fix.
;;
;; ## What the /qa reduction established (S98 Stage-1, 2026-07-01)
;;
;; FIXME 0486's diagnostic proposed a still-smaller `redA` shape — "launch +
;; send-conn + churned STRING body, no grids/vec" — on the theory that the freed-
;; early buffer is the pure `Response.body` heap String. **That shape does NOT
;; reproduce** (measured 0/8 SIGABRT, two variants incl. a heavy two-live-String
;; render). Reduction findings, all measured against `target/debug/cranelisp` on
;; this fixture family (8 trials each, `Stdio::null`, one read-to-EOF request):
;;
;;   - churned String body, NO vec ............................. 0/8 (clean)
;;   - two heavy live Strings, interleaved render, NO vec ...... 0/8 (clean)
;;   - SINGLE live `(Vec Int)`, render via `get` only ......... 0/8 (clean)
;;   - TWO live `(Vec Int)` (build + `assoc`-churn), render ... 8/8 SIGABRT  ← this
;;   - full grid (Cell+Grid ADT wrap over the two vecs) ....... 8/8 SIGABRT  (sibling)
;;
;; So the load-bearing floor is: (1) a `(Vec …)` reached through the borrowed-Var-
;; param wrappers (`ring2-rc.md §5.5`), AND (2) TWO vecs BOTH live simultaneously
;; (the `build` original `g` + the `assoc`-churned `s`) — a single live vec is not
;; enough. The `Cell`/`Grid` ADT wrapper is NOT load-bearing (dropped here); the
;; pure-String `Response.body` UAF hypothesis is REFUTED. This refines the fix
;; target toward the borrowed-Var vec RC path on the launched strand, and is fed
;; back to /arch + /backend on FIXME 0486. Both this guard and its grid sibling
;; stay RED until /backend lands the keep-alive fix (invariant 15).
;;
;; NOTE (size): the reduction above was at vec-size 81 (isolation-deterministic).
;; This committed fixture uses size 400 so the deferred-send window is wide enough
;; to fire reliably under FULL-suite parallel contention (a single 81-size request
;; can go false-GREEN at 1795-way parallelism); the test also drives a burst + polls
;; for the abort. See `tests/launch_vec_send_corrupt.rs` header for the determinism
;; record.
;;
;; Free-standing: primitives + the `web` platform leaves only, ZERO stdlib.

(platform web)
(import [primitives [bind sleep vec-get vec-set vec-push int-to-string str-concat sub-i64 le-i64 Int]])
(import [serve [listen accept]])
(import [platform.web [read-conn send-conn]])
(import [web [Request Response]])

;; Borrowed-Var-param wrappers (ring2-rc.md §5.5) — the extra call frame is the
;; load-bearing RC path (exactly as stdlib collections.vec get/assoc/conj wrap
;; vec-get/vec-set/vec-push). NO ADT wrapper this time.
(defn get [v :Int i] (vec-get v i))
(defn assoc [v :Int i x] (vec-set v i x))
(defn conj [v x] (vec-push v x))

(defn build [v i] (if (le-i64 i 0) v (build (conj v i) (sub-i64 i 1))))
;; churn derives a SECOND vec via assoc (vec-set on a Var param) — g and s are
;; BOTH live during the render below (the load-bearing two-live-vec shape).
(defn churn [v i] (if (le-i64 i 0) v (churn (assoc v (sub-i64 i 1) i) (sub-i64 i 1))))

(defn render [a b i acc]
  (if (le-i64 i 0) acc
    (render a b (sub-i64 i 1)
      (str-concat acc (str-concat (int-to-string (get a (sub-i64 i 1)))
                                  (int-to-string (get b (sub-i64 i 1))))))))

;; PURE — computed as the argument to the `send-conn` leaf inside the launched
;; strand. g (original) and s (assoc-churned) are BOTH live during render. Sizes
;; are large (400) so each launched request does heavy vec + string churn — this
;; widens the deferred-send corruption window enough that it fires reliably even
;; under full-suite parallel contention (the smaller 81-size shape's window can
;; close under 1795-way parallelism; see the .rs header determinism note).
(defn make-resp [req]
  (let [g (build [] 400)
        s (churn g 400)]
    (Response 200 "text/html" (render g s 400 ""))))

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
