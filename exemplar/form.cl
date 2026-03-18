;; form.cl — URL-encoded form body parsing for the Sudoku solver
;;
;; Parses the POST body from the HTML form into an 81-character puzzle
;; string suitable for make-grid. The form has 81 fields named c00
;; through c88 (row, col). Each field value is either a digit (1-9)
;; or empty. Empty values become dots in the puzzle string.
;;
;; Example: "c00=5&c01=&c02=3&..." -> "5.3..."
;;
;; Depends on: prelude
;; Uses: split, str-eq, str-len, char-at, str-concat, int-to-string, parse-int

;; ── URL decoding ─────────────────────────────────────────────────────

;; Minimal URL decoding: replace + with space.
;; Full %XX decoding is not needed because form values are single digits
;; or empty. The browser URL-encodes the POST body, but digits and empty
;; strings don't need percent-encoding.
(defn url-decode [s]
  (replace s "+" " "))

;; ── Puzzle string construction ───────────────────────────────────────

;; Initialize an 81-character string of dots.
(defn make-dots-helper [i acc]
  (if (eq-i64 i 81) acc
    (make-dots-helper (add-i64 i 1) (str-concat acc "."))))

(defn make-dots []
  (make-dots-helper 0 ""))

;; Parse a digit character to its integer value (0-9), or -1 if not a digit.
(defn parse-digit-char [ch]
  (cond
    (str-eq ch "0") 0
    (str-eq ch "1") 1
    (str-eq ch "2") 2
    (str-eq ch "3") 3
    (str-eq ch "4") 4
    (str-eq ch "5") 5
    (str-eq ch "6") 6
    (str-eq ch "7") 7
    (str-eq ch "8") 8
    (str-eq ch "9") 9
    -1))

;; Set a character in an 81-char puzzle string at position idx.
;; Rebuilds the string: prefix + ch + suffix.
(defn set-char-at [s idx ch]
  (str-concat (substring s 0 idx)
    (str-concat ch (substring s (add-i64 idx 1) (str-len s)))))

;; ── Form body parsing ────────────────────────────────────────────────

;; Extract row and column from a field name like "c35".
;; Returns the flat index (row * 9 + col), or -1 if the name is invalid.
;; Expected format: 'c' followed by exactly two digit characters.
(defn parse-field-index [name]
  (if (lt-i64 (str-len name) 3) -1
    (if (not (str-eq (char-at name 0) "c")) -1
      (let [row (parse-digit-char (char-at name 1))
            col (parse-digit-char (char-at name 2))]
        (if (lt-i64 row 0) -1
          (if (lt-i64 col 0) -1
            (if (gt-i64 row 8) -1
              (if (gt-i64 col 8) -1
                (add-i64 (mul-i64 row 9) col)))))))))

;; Process a single key=value pair and update the puzzle string.
;; If the value is a digit (1-9), place it at the correct position.
;; If the value is empty or not a digit, leave the dot.
(defn process-pair [puzzle pair]
  (let [parts (split pair "=")]
    (if (lt-i64 (vec-len parts) 1) puzzle
      (let [key (vec-get parts 0)
            idx (parse-field-index key)]
        (if (lt-i64 idx 0) puzzle
          (if (lt-i64 (vec-len parts) 2) puzzle
            (let [val (vec-get parts 1)]
              (if (eq-i64 (str-len val) 0) puzzle
                ;; Value is non-empty: check if it's a valid digit 1-9
                (let [ch (char-at val 0)]
                  (let [d (parse-digit-char ch)]
                    (if (lt-i64 d 1) puzzle
                      (if (gt-i64 d 9) puzzle
                        (set-char-at puzzle idx ch)))))))))))))

;; Process all key=value pairs from the split body.
(defn process-pairs-helper [puzzle pairs i]
  (if (eq-i64 i (vec-len pairs)) puzzle
    (process-pairs-helper
      (process-pair puzzle (vec-get pairs i))
      pairs
      (add-i64 i 1))))

;; Parse a URL-encoded form body into an 81-character puzzle string.
;; The body contains fields c00=X&c01=Y&...&c88=Z where X,Y,Z are
;; digits (1-9) or empty. Empty values become dots.
(defn parse-form-body [body]
  (let [decoded (url-decode body)
        pairs (split decoded "&")
        puzzle (make-dots)]
    (process-pairs-helper puzzle pairs 0)))

;; ── Tests ─────────────────────────────────────────────────────────────

(mod test
  (import [super [*]])

  ;; Test parsing a simple form body with a few digits
  (defn test-parse-simple []
    (let [body "c00=5&c02=3"
          result (parse-form-body body)]
      ;; Position 0 should be '5', position 2 should be '3', rest dots
      (if (if (str-eq (char-at result 0) "5")
            (str-eq (char-at result 2) "3")
            false)
        1 0)))

  ;; Test that empty values produce dots
  (defn test-empty-values-produce-dots []
    (let [body "c00=&c01=&c02="
          result (parse-form-body body)]
      ;; All three should be dots
      (if (if (str-eq (char-at result 0) ".")
            (if (str-eq (char-at result 1) ".")
              (str-eq (char-at result 2) ".")
              false)
            false)
        1 0)))

  ;; Test result is exactly 81 characters
  (defn test-result-length []
    (let [result (parse-form-body "c00=5")]
      (if (eq-i64 (str-len result) 81) 1 0)))

  ;; Test url-decode replaces + with space
  (defn test-url-decode []
    (if (str-eq (url-decode "hello+world") "hello world") 1 0))

  ;; Test parse-field-index with valid name
  (defn test-field-index-valid []
    ;; c35 -> row 3, col 5 -> index 32
    (if (eq-i64 (parse-field-index "c35") 32) 1 0))

  ;; Test parse-field-index with invalid name
  (defn test-field-index-invalid []
    (if (eq-i64 (parse-field-index "x00") -1) 1 0))

  ;; Test that all 81 positions are addressable
  (defn test-last-position []
    (let [body "c88=7"
          result (parse-form-body body)]
      ;; Position 80 (row 8, col 8) should be '7'
      (if (str-eq (char-at result 80) "7") 1 0)))

  ;; Test with a more realistic body fragment
  (defn test-multiple-digits []
    (let [body "c00=5&c01=3&c10=6&c11=&c20=9"
          result (parse-form-body body)]
      ;; c00=5 -> idx 0, c01=3 -> idx 1, c10=6 -> idx 9,
      ;; c11= -> idx 10 (dot), c20=9 -> idx 18
      (if (if (str-eq (char-at result 0) "5")
            (if (str-eq (char-at result 1) "3")
              (if (str-eq (char-at result 9) "6")
                (if (str-eq (char-at result 10) ".")
                  (str-eq (char-at result 18) "9")
                  false)
                false)
              false)
            false)
        1 0)))

  ;; --- Main: sum all test results ---

  (defn main []
    (add-i64 (test-parse-simple)
      (add-i64 (test-empty-values-produce-dots)
        (add-i64 (test-result-length)
          (add-i64 (test-url-decode)
            (add-i64 (test-field-index-valid)
              (add-i64 (test-field-index-invalid)
                (add-i64 (test-last-position)
                  (test-multiple-digits))))))))))
