;; L-B1 golden-CLIF corpus 07 — trait declaration + impls + static dispatch.
;; Free-standing (trait defined inline, no stdlib); green by construction.
(import [primitives [*]])

(deftrait Sizeable
  (size [a] Int))

(deftype Box (MkBox [:Int w]))
(deftype Tag (MkTag [:String label]))

(impl Sizeable Box (defn size [b] (match b [(MkBox w) w])))
(impl Sizeable Tag (defn size [t] (match t [(MkTag s) (str-len s)])))

(defn main []
  (Pure (add-i64 (size (MkBox 5)) (size (MkTag "abc")))))
