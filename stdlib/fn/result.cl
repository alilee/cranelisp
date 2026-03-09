;; fn/result.cl — Result type
;;
;; The Result type represents a computation that can succeed (Ok) or fail
;; (Err). Used for error handling without exceptions.
;;
;; Spec: plan-stdlib.md §3.3

(deftype (Result a e) (Ok [:a val]) (Err [:e err]))

(defn is-ok? "Test if a Result is Ok" [r]
  (match r
    [(Ok _) true
     (Err _) false]))

(defn is-err? "Test if a Result is Err" [r]
  (match r
    [(Ok _) false
     (Err _) true]))

(defn unwrap-or "Extract Ok value or return default" [default r]
  (match r
    [(Ok v) v
     (Err _) default]))

(defn map-ok "Apply function to Ok value, pass through Err" [f r]
  (match r
    [(Ok v) (Ok (f v))
     (Err e) (Err e)]))

(defn map-err "Apply function to Err value, pass through Ok" [f r]
  (match r
    [(Ok v) (Ok v)
     (Err e) (Err (f e))]))

(defn and-then "Chain a fallible computation on Ok value" [f r]
  (match r
    [(Ok v) (f v)
     (Err e) (Err e)]))
