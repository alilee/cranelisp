;; text/string.cl — String operations and str macro
;;
;; Higher-level string functions built on the Ring 1 string primitives.
;; The 11 primitives (substring, char-at, split, join, replace, trim,
;; starts-with?, ends-with?, contains?, to-upper, to-lower) plus
;; str-len, str-concat, str-eq are auto-available from the primitives
;; module. This module provides additional convenience functions.
;;
;; Also provides the `str` macro for concatenating string representations.
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])

;; Macro bodies use qualified macros/ names so expansion results are
;; independent of the call-site's imports (spec §9.1.3).
(defmacro str "Concatenate string representations of all arguments"
  ([] (macros/SexpStr ""))
  ([x] `(show ~x))
  ([x &rest] `(str-concat (show ~x) (str ~@rest))))

(defn blank? "Test if a string is empty or contains only whitespace"
  [:String s] :Bool
  (str-eq (trim s) ""))

(defn repeat-str "Repeat a string n times"
  [:String s :Int n] :String
  (if (le-i64 n 0) ""
    (str-concat s (repeat-str s (sub-i64 n 1)))))

(defn index-of "Find the index of the first occurrence of substr, or -1 if not found"
  [:String s :String substr] :Int
  (let [slen (str-len s)
        sublen (str-len substr)]
    (if (gt-i64 sublen slen) -1
      (index-of-loop s substr slen sublen 0))))

(defn- index-of-loop "Helper loop for index-of"
  [:String s :String substr :Int slen :Int sublen :Int i] :Int
  (if (gt-i64 (add-i64 i sublen) slen) -1
    (if (str-eq (substring s i (add-i64 i sublen)) substr) i
      (index-of-loop s substr slen sublen (add-i64 i 1)))))

(defn reverse-str "Reverse a string character by character"
  [:String s] :String
  (let [len (str-len s)]
    (if (le-i64 len 0) ""
      (reverse-str-loop s (sub-i64 len 1) ""))))

(defn- reverse-str-loop "Helper loop for reverse-str"
  [:String s :Int i :String acc] :String
  (if (lt-i64 i 0) acc
    (reverse-str-loop s (sub-i64 i 1) (str-concat acc (char-at s i)))))

(defn pad-left "Pad a string on the left to the given width with the pad character"
  [:String s :Int width :String pad] :String
  (let [len (str-len s)]
    (if (ge-i64 len width) s
      (str-concat (repeat-str pad (sub-i64 width len)) s))))

(defn pad-right "Pad a string on the right to the given width with the pad character"
  [:String s :Int width :String pad] :String
  (let [len (str-len s)]
    (if (ge-i64 len width) s
      (str-concat s (repeat-str pad (sub-i64 width len))))))
