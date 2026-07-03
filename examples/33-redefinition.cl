;; 33-redefinition.cl -- Redefinition: definitions are live
;;
;; A Cranelisp program is a sequence of definitions, and definitions are
;; LIVE. A later `defn` for a name does not shadow the earlier one — it
;; REPLACES it. And replacement is not just for future code: every
;; EXISTING dependent (any function already defined in terms of that
;; name) rebinds to the new definition automatically. There is no stale
;; copy anywhere; by the time `main` runs, every call site — however
;; early it was written — sees the latest definition of every name it
;; uses.
;;
;; This is the same behaviour the REPL gives you interactively: redefine
;; a helper and everything built on top of it picks up the change. In a
;; batch file the observable consequence is that the LAST definition of
;; a name is the one that runs, everywhere.
;;
;; This example demonstrates three consequences:
;;   1. A direct call uses the latest definition (the later defn won).
;;   2. A dependent defined against the OLD definition rebinds to the
;;      new one.
;;   3. Rebinding cascades transitively through a chain of dependents.
;;
;; Expected exit code: 136 (6 + 18 + 112).

;; --- 1 + 2: a definition, a dependent, and a replacement --------------

;; First definition: step adds one.
(defn step [x] (add-i64 x 1))

;; A dependent, written while `step` still meant "add one". If `twice`
;; kept the definition it was written against, (twice 2) would be 4.
(defn twice [x] (step (step x)))

;; Redefinition: `step` now means "triple". This REPLACES the earlier
;; definition — and `twice`, already defined above, rebinds to it.
(defn step [x] (mul-i64 x 3))

;; Direct call: the later defn is the one that runs. (step 2) = 6.
(defn test-direct [] (step 2))

;; The dependent sees the new step too: (twice 2) = 3 * (3 * 2) = 18,
;; not the 4 its source order might suggest.
(defn test-rebind [] (twice 2))

;; --- 3: rebinding cascades through a dependency chain -----------------

;; A three-deep chain, each layer defined before `base` is replaced.
(defn base [] 1)
(defn mid  [] (add-i64 (base) 10))
(defn top  [] (add-i64 (mid) 100))

;; Replace the leaf. Nothing that mentions `mid` or `top` is touched,
;; yet both now compute with the new `base`.
(defn base [] 2)

;; (top) = 100 + (10 + 2) = 112 — the new base, two layers down.
(defn test-transitive [] (top))

;; --- Summing results ---------------------------------------------------

;; Expected: 6 + 18 + 112 = 136
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-direct)
      (add-i64 (test-rebind)
               (test-transitive)))))
