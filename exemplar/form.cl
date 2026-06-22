;; form.cl — URL-encoded form body parsing for the Sudoku solver
;;
;; Parses the POST body from the HTML form into an 81-character puzzle
;; string suitable for make-grid. The form has 81 fields named c00
;; through c88 (row, col). Each field value is either a digit (1-9)
;; or empty. Empty values become dots in the puzzle string.
;;
;; Example: "c00=5&c01=&c02=3&..." -> "5.3..."
;;
;; Depends on: prelude (traits, operators, the `cond` macro)
;;
;; Idiomatic surface (S86 de-leak): arithmetic/comparison via prelude trait
;; operators; `=` on String is Eq dispatch. The string primitives
;; (`char-at`, `str-len`, `str-concat`, `substring`, `split`, `replace`) are
;; imported by name; Vec access goes through curated `count`/`get`. No grid
;; building here, so the DEF-2 `conj` carve-out does not apply.

(import [collections.vec [count get]])
(import [primitives [char-at str-len str-concat substring split replace not]])
;; S88 G8 adoption: the recursive make-dots loop is replaced by the stdlib
;; `text.string/repeat-str`.
(import [text.string [repeat-str]])

;; ── URL decoding ─────────────────────────────────────────────────────

;; Minimal URL decoding: replace + with space.
;; Full %XX decoding is not needed because form values are single digits
;; or empty. The browser URL-encodes the POST body, but digits and empty
;; strings don't need percent-encoding.
(defn url-decode [s]
  (replace s "+" " "))

;; ── Puzzle string construction ───────────────────────────────────────

;; Initialize an 81-character string of dots.
;; S88 G8 adoption: was a hand-rolled recursive str-concat loop; now the
;; stdlib one-liner.
(defn make-dots []
  (repeat-str "." 81))

;; Parse a digit character to its integer value (0-9), or -1 if not a digit.
(defn parse-digit-char [ch]
  (cond
    (= ch "0") 0
    (= ch "1") 1
    (= ch "2") 2
    (= ch "3") 3
    (= ch "4") 4
    (= ch "5") 5
    (= ch "6") 6
    (= ch "7") 7
    (= ch "8") 8
    (= ch "9") 9
    -1))

;; Set a character in an 81-char puzzle string at position idx.
;; Rebuilds the string: prefix + ch + suffix.
(defn set-char-at [s idx ch]
  (str-concat (substring s 0 idx)
    (str-concat ch (substring s (+ idx 1) (str-len s)))))

;; ── Form body parsing ────────────────────────────────────────────────

;; Extract row and column from a field name like "c35".
;; Returns the flat index (row * 9 + col), or -1 if the name is invalid.
;; Expected format: 'c' followed by exactly two digit characters.
(defn parse-field-index [name]
  (if (< (str-len name) 3) -1
    (if (not (= (char-at name 0) "c")) -1
      (let [row (parse-digit-char (char-at name 1))
            col (parse-digit-char (char-at name 2))]
        (if (< row 0) -1
          (if (< col 0) -1
            (if (> row 8) -1
              (if (> col 8) -1
                (+ (* row 9) col)))))))))

;; Process a single key=value pair and update the puzzle string.
;; If the value is a digit (1-9), place it at the correct position.
;; If the value is empty or not a digit, leave the dot.
(defn process-pair [puzzle pair]
  (let [parts (split pair "=")]
    (if (< (count parts) 1) puzzle
      (let [key (get parts 0)
            idx (parse-field-index key)]
        (if (< idx 0) puzzle
          (if (< (count parts) 2) puzzle
            (let [val (get parts 1)]
              (if (= (str-len val) 0) puzzle
                ;; Value is non-empty: check if it's a valid digit 1-9
                (let [ch (char-at val 0)]
                  (let [d (parse-digit-char ch)]
                    (if (< d 1) puzzle
                      (if (> d 9) puzzle
                        (set-char-at puzzle idx ch)))))))))))))

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
;; Test functions are top-level `test-*` defns returning `(Option String)`
;; per repl/spec.md §16.1. Discoverable via `(discover-tests)`,
;; runnable via `(run-test ...)` — Decision 30 safe pattern (c). No
;; `(mod test ...)` wrapper, no `(import [super [*]])`.

;; Test parsing a simple form body with a few digits
(defn test-parse-simple []
  (let [body "c00=5&c02=3"
        result (parse-form-body body)]
    ;; Position 0 should be '5', position 2 should be '3', rest dots
    (if (= (char-at result 0) "5")
      (if (= (char-at result 2) "3") None
        (Some "position 2 should be '3'"))
      (Some "position 0 should be '5'"))))

;; Test that empty values produce dots
(defn test-empty-values-produce-dots []
  (let [body "c00=&c01=&c02="
        result (parse-form-body body)]
    (if (= (char-at result 0) ".")
      (if (= (char-at result 1) ".")
        (if (= (char-at result 2) ".") None
          (Some "position 2 should be a dot"))
        (Some "position 1 should be a dot"))
      (Some "position 0 should be a dot"))))

;; Test result is exactly 81 characters
(defn test-result-length []
  (let [result (parse-form-body "c00=5")]
    (if (= (str-len result) 81) None
      (Some "parse-form-body result should be 81 chars long"))))

;; Test url-decode replaces + with space
(defn test-url-decode []
  (if (= (url-decode "hello+world") "hello world") None
    (Some "url-decode should replace + with space")))

;; Test parse-field-index with valid name
(defn test-field-index-valid []
  ;; c35 -> row 3, col 5 -> index 32
  (if (= (parse-field-index "c35") 32) None
    (Some "parse-field-index of 'c35' should be 32")))

;; Test parse-field-index with invalid name
(defn test-field-index-invalid []
  (if (= (parse-field-index "x00") -1) None
    (Some "parse-field-index of 'x00' should be -1")))

;; Test that all 81 positions are addressable
(defn test-last-position []
  (let [body "c88=7"
        result (parse-form-body body)]
    ;; Position 80 (row 8, col 8) should be '7'
    (if (= (char-at result 80) "7") None
      (Some "position 80 should be '7'"))))

;; Test with a more realistic body fragment
(defn test-multiple-digits []
  (let [body "c00=5&c01=3&c10=6&c11=&c20=9"
        result (parse-form-body body)]
    ;; c00=5 -> idx 0, c01=3 -> idx 1, c10=6 -> idx 9,
    ;; c11= -> idx 10 (dot), c20=9 -> idx 18
    (if (= (char-at result 0) "5")
      (if (= (char-at result 1) "3")
        (if (= (char-at result 9) "6")
          (if (= (char-at result 10) ".")
            (if (= (char-at result 18) "9") None
              (Some "idx 18 should be '9'"))
            (Some "idx 10 should be '.'"))
          (Some "idx 9 should be '6'"))
        (Some "idx 1 should be '3'"))
      (Some "idx 0 should be '5'"))))
