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
(import [primitives [*]])

;; Macro bodies use qualified macros/ names so expansion results are
;; independent of the call-site's imports (spec §9.1.3).
(defmacro str "Concatenate string representations of all arguments"
  ([] (macros/SexpStr ""))
  ([x] `(show ~x))
  ([x &rest] `(primitives/str-concat (show ~x) (str ~@rest))))

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

;; ── char<->digit — Stage C.1 gap G4 ──────────────────────────────────
;; `char-to-digit` maps a single-character decimal-digit string to its Int
;; value, returning the sentinel -1 for any non-digit (so callers branch on
;; `(< d 0)` rather than crash). `digit-to-char` is the inverse for 0..9.
;; Both are direct compositions over the digit table "0123456789" — no new
;; primitive. They collapse the exemplar's N-way cond/if char-to-int ladders
;; (form.cl parse-digit-char, grid.cl make-grid-helper).
;;
;; NAMING NOTE: the C.1 gap proposed `char->digit`/`digit->char`, but a `defn`
;; NAME containing `->` does not parse on the current binary (the reader
;; treats `->` as the threading macro head: `(defn char->digit "doc" […])`
;; ⇒ `parse error … defn: expected params [...]`). The `-to-` spelling is the
;; stdlib choice that avoids the collision; the verb is otherwise identical.
;; Defect handoff filed for the `->`-in-defn-name parse failure (plan §26.4).

(defn char-to-digit "Decimal digit char 0-9 to its Int value, or -1 if not a digit"
  [:String ch] :Int
  (if (eq-i64 (str-len ch) 1)
    (index-of "0123456789" ch)
    -1))

(defn digit-to-char "Int 0-9 to its single-character string, or empty if out of range"
  [:Int d] :String
  (if (lt-i64 d 0) ""
    (if (gt-i64 d 9) ""
      (substring "0123456789" d (add-i64 d 1)))))

;; ── replace-at / str-assoc — Stage C.1 gap G5 ────────────────────────
;; Functional string-index set: return `s` with the character at `idx`
;; replaced by `ch` (a single-character string). Composed from
;; `substring`/`str-concat`. `str-assoc` is the Clojure-aligned alias
;; (matching collections `assoc`'s "set at key" shape). Out-of-range `idx`
;; returns `s` unchanged. Collapses the exemplar's set-char-at (form.cl).

(defn replace-at "Return s with the character at idx replaced by ch (single char)"
  [:String s :Int idx :String ch] :String
  (let [len (str-len s)]
    (if (lt-i64 idx 0) s
      (if (ge-i64 idx len) s
        (str-concat (substring s 0 idx)
          (str-concat ch (substring s (add-i64 idx 1) len)))))))

(defn str-assoc "Clojure-aligned alias for replace-at: set the char at idx"
  [:String s :Int idx :String ch] :String
  (replace-at s idx ch))

;; ── Self-tests ───────────────────────────────────────────────────────
;; `(mod test …)` submodule (S87 Stage C.2): exercises the string helpers with
;; the in-language harness (String has Eq + Display).

(mod- test)
