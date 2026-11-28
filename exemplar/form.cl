;; form.cl — URL-encoded form body parsing for the Sudoku solver
;;
;; Parses the POST body from the HTML form into an 81-character puzzle
;; string suitable for make-grid. The form has 81 fields named c00
;; through c88 (row, col). Each field value is either a digit (1-9)
;; or empty. Empty values become dots in the puzzle string.
;;
;; Example: "c00=5&c01=&c02=3&..." -> "5.3..."

(import [collections.vec [count get]])
(import [primitives [char-at str-len str-concat substring split replace not]])
(import [text.string [repeat-str char-to-digit replace-at]])
(import [testing.assertions [check assert-eq]])

;; ── URL decoding ─────────────────────────────────────────────────────

;; Minimal URL decoding: replace + with space.
;; Full %XX decoding is not needed because form values are single digits
;; or empty. The browser URL-encodes the POST body, but digits and empty
;; strings don't need percent-encoding.
(defn url-decode [s]
  (replace s "+" " "))

;; ── Puzzle string construction ───────────────────────────────────────

;; Initialize an 81-character string of dots.
(defn make-dots []
  (repeat-str "." 81))

;; ── Form body parsing ────────────────────────────────────────────────

;; Extract row and column from a field name like "c35".
;; Returns the flat index (row * 9 + col), or -1 if the name is invalid.
;; Expected format: 'c' followed by exactly two digit characters.
(defn parse-field-index [name]
  (if (< (str-len name) 3) -1
    (if (not (= (char-at name 0) "c")) -1
      (let [row (char-to-digit (char-at name 1))
            col (char-to-digit (char-at name 2))]
        (if (< row 0) -1
          (if (< col 0) -1
            (if (> row 8) -1
              (if (> col 8) -1
                (+ (* row 9) col)))))))))

;; Process a single key=value pair and update the puzzle string.
;; If the value is a digit (1-9), place it at the correct position.
;; If the value is empty or not a digit, leave the dot.
;; The pair comes from the request body, so it may hold anything: the one
;; `count` guard bounds both `get`s, which is what keeps a malformed body from
;; panicking the server (a panic ends the process).
(defn process-pair [puzzle pair]
  (let [parts (split pair "=")]
    (if (< (count parts) 2) puzzle
      (let [idx (parse-field-index (get parts 0))
            val (get parts 1)]
        (if (< idx 0) puzzle
          (if (= (str-len val) 0) puzzle
            (let [ch (char-at val 0)]
              (if (< (char-to-digit ch) 1) puzzle
                (replace-at puzzle idx ch)))))))))

;; Process all key=value pairs from the split body.
(defn process-pairs-helper [puzzle pairs i]
  (if (= i (count pairs)) puzzle
    (process-pairs-helper
      (process-pair puzzle (get pairs i))
      pairs
      (+ i 1))))

;; Parse a URL-encoded form body into an 81-character puzzle string.
;; The body contains fields c00=X&c01=Y&...&c88=Z where X,Y,Z are
;; digits (1-9) or empty. Empty values become dots.
(defn parse-form-body [body]
  (let [decoded (url-decode body)
        pairs (split decoded "&")
        puzzle (make-dots)]
    (process-pairs-helper puzzle pairs 0)))

;; ── Tests ─────────────────────────────────────────────────────────────
;;
;; Each `test-*` returns `(Option String)`, `None` for a pass
;; (repl/spec/16-test-discovery.md §16.1). `tests.cl` calls them, and
;; `cranelisp --test` discovers them.

(defn test-parse-simple []
  (let [result (parse-form-body "c00=5&c02=3")]
    (check
      (assert-eq "5" (char-at result 0))
      (assert-eq "." (char-at result 1))
      (assert-eq "3" (char-at result 2)))))

(defn test-empty-values-produce-dots []
  (assert-eq "..." (substring (parse-form-body "c00=&c01=&c02=") 0 3)))

(defn test-result-length []
  (assert-eq 81 (str-len (parse-form-body "c00=5"))))

(defn test-url-decode []
  (assert-eq "hello world" (url-decode "hello+world")))

;; c35 is row 3, column 5: index 32.
(defn test-field-index-valid []
  (assert-eq 32 (parse-field-index "c35")))

(defn test-field-index-invalid []
  (check
    (assert-eq -1 (parse-field-index "x00"))
    (assert-eq -1 (parse-field-index "c9"))
    (assert-eq -1 (parse-field-index "c90"))))

;; c88 is the last cell, index 80.
(defn test-last-position []
  (assert-eq "7" (char-at (parse-form-body "c88=7") 80)))

;; c00 → 0, c01 → 1, c10 → 9, c11 (empty) → 10, c20 → 18.
(defn test-multiple-digits []
  (let [result (parse-form-body "c00=5&c01=3&c10=6&c11=&c20=9")]
    (check
      (assert-eq "53......." (substring result 0 9))
      (assert-eq "6........9" (substring result 9 19)))))

;; A body a browser would never send must still parse without a panic: a bare
;; key, an empty pair, extra `=`, a field name out of range or too short, a
;; non-digit value, a multi-byte value. Only `c11=4=x` places a digit.
(defn test-malformed-body []
  (assert-eq (str-concat (substring (make-dots) 0 10)
               (str-concat "4" (substring (make-dots) 0 70)))
    (parse-form-body "c00&=&==&c0=5&c99=1&c11=4=x&c22=x&c33=é&&c44")))
