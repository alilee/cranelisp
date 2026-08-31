;; L-B1 golden-CLIF corpus 10 — a match mixing a NULLARY-constructor arm with a
;; boxed arm, beside its all-boxed control, in ONE module (FIXME 0917).
;;
;; The committed repro program of `tests/nullary_arm_beside_boxed_arm_0917.rs`,
;; with the repro's two children folded into one module so both `step` frames
;; land in the same capture and the subject's return seam can be read directly
;; against the control's. The subject/control axis is what it is in the repro —
;; `step`'s returned constructors, one token — and nothing else differs. The
;; `None` arms are never taken at runtime; their presence alone is the defect.
;; What the entry pins is that seam: after the fix the two must agree.
;;
(import [primitives [*]])

(deftype Item (A [:Int a]) (B [:Int b]))
(deftype Box [:(Vec Item) items])

(defn item-at [bx i] (match bx [(Box items) (vec-get items i)]))
(defn set-item [bx i it] (match bx [(Box items) (Box (vec-set items i it))]))

;; SUBJECT — one nullary arm (`None`) beside the boxed `(Some …)` arms.
(defn subject-step [bx i d]
  (let [it (item-at bx i)]
    (match it
      [(A x) (if (eq-i64 x d) None (Some (set-item bx i (A d))))
       (B x) None])))

;; CONTROL — identical except that no arm returns a nullary constructor.
(defn control-step [bx i d]
  (let [it (item-at bx i)]
    (match it
      [(A x) (if (eq-i64 x d) (Some bx) (Some (set-item bx i (A d))))
       (B x) (Some bx)])))

(defn subject-loop [bx n acc]
  (if (eq-i64 n 0) acc
    (match (subject-step bx 0 5)
      [(Some b2) (subject-loop bx (sub-i64 n 1) (add-i64 acc 1)) None acc])))

(defn control-loop [bx n acc]
  (if (eq-i64 n 0) acc
    (match (control-step bx 0 5)
      [(Some b2) (control-loop bx (sub-i64 n 1) (add-i64 acc 1)) None acc])))

(defn main []
  (Pure (add-i64 (subject-loop (Box [(A 1) (A 2) (A 3)]) 100 0)
                 (control-loop (Box [(A 1) (A 2) (A 3)]) 100 0))))
