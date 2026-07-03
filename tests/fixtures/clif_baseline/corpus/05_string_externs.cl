;; L-B1 golden-CLIF corpus 05 — string externs (the Decision-24 consuming
;; convention surface; the str-len$borrowed sibling's B3.5 re-baseline lands
;; here). Free-standing; green by construction.
(import [primitives [*]])

(defn shout [:String s] (to-upper (str-concat s "!")))

(defn main []
  (let [s (shout "abc")]
    (Pure (add-i64 (str-len s) (str-len (substring s 0 2))))))
