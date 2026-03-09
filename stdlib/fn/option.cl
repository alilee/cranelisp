;; fn/option.cl — Option type
;;
;; The Option type represents a value that may or may not be present.
;; None indicates absence; Some wraps a present value.
;;
;; Spec: 06-adt.md §6.1

(deftype (Option a) None (Some [:a val]))
