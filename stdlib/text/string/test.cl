;; text/string/test.cl — self-tests for text.string (module text.string.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. Exercises the string helpers plus the new `char-to-digit`/
;; `digit-to-char` (gap G4) and `replace-at`/`str-assoc` (gap G5).

(import [super [blank? repeat-str index-of reverse-str pad-left pad-right
                char-to-digit digit-to-char replace-at str-assoc]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [primitives [Option String]])

(defn test-blank-empty [] :(Option String)
  (assert-true (blank? "")))

(defn test-not-blank [] :(Option String)
  (assert-false (blank? "x")))

(defn test-repeat-str [] :(Option String)
  (assert-eq "aaa" (repeat-str "a" 3)))

(defn test-index-of [] :(Option String)
  (assert-eq 2 (index-of "abcde" "cd")))

(defn test-index-of-absent [] :(Option String)
  (assert-eq -1 (index-of "abc" "z")))

(defn test-reverse-str [] :(Option String)
  (assert-eq "cba" (reverse-str "abc")))

(defn test-pad-left [] :(Option String)
  (assert-eq "..ab" (pad-left "ab" 4 ".")))

;; char-to-digit / digit-to-char — G4
(defn test-char-to-digit [] :(Option String)
  (assert-eq 7 (char-to-digit "7")))

(defn test-char-to-digit-non-digit [] :(Option String)
  (assert-eq -1 (char-to-digit "x")))

(defn test-char-to-digit-multichar [] :(Option String)
  (assert-eq -1 (char-to-digit "12")))

(defn test-digit-to-char [] :(Option String)
  (assert-eq "3" (digit-to-char 3)))

(defn test-digit-to-char-out-of-range [] :(Option String)
  (assert-eq "" (digit-to-char 10)))

(defn test-char-digit-roundtrip [] :(Option String)
  (assert-eq 5 (char-to-digit (digit-to-char 5))))

;; replace-at / str-assoc — G5
(defn test-replace-at [] :(Option String)
  (assert-eq "aXc" (replace-at "abc" 1 "X")))

(defn test-replace-at-first [] :(Option String)
  (assert-eq "Xbc" (replace-at "abc" 0 "X")))

(defn test-replace-at-out-of-range [] :(Option String)
  (assert-eq "abc" (replace-at "abc" 9 "X")))

(defn test-str-assoc-alias [] :(Option String)
  (assert-eq "aXc" (str-assoc "abc" 1 "X")))
