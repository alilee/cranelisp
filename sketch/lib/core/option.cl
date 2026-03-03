(mod collections)
(import [primitives [*] collections [Functor fmap]])

;; ── Option Type ─────────────────────────────────────

(deftype (Option a) "An optional value, either None or Some"
  (None "Represents absence of a value")
  (Some "Wraps a present value" [:a val]))

;; ── Functor Option ──────────────────────────────────

(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))
