;; 09-strings.cl -- String literals and string operations
;;
;; Strings are heap-allocated sequences of bytes, managed by reference counting.
;; String literals are written in double quotes: "hello"
;;
;; String primitives used here (the `primitives` module exposes more —
;; `substring`, `split`, `trim`, `parse-int` and friends; those are not
;; yet taught by this sequence):
;;   str-concat    (String -> String -> String)  concatenate two strings
;;   str-eq        (String -> String -> Bool)     string equality
;;   str-len       (String -> Int)                string length in bytes
;;   int-to-string (Int -> String)                integer to string
;;   float-to-string (Float -> String)            float to string
;;   bool-to-string  (Bool -> String)             boolean to "true"/"false"
;;
;; Since batch programs return Int from main, we use str-len and str-eq
;; to convert string results to integers for verification.

;; String literal length
(defn test-literal-len [] (str-len "hello"))

;; Empty string has length zero
(defn test-empty-len [] (str-len ""))

;; Concatenation produces a new string
(defn test-concat []
  (str-len (str-concat "hello" " world")))

;; Chained concatenation
(defn test-concat-chain []
  (str-len (str-concat (str-concat "a" "b") "c")))

;; String equality: same content
(defn test-eq-same []
  (if (str-eq "abc" "abc") 1 0))

;; String equality: different content
(defn test-eq-diff []
  (if (str-eq "abc" "xyz") 1 0))

;; Convert an integer to a string
(defn test-int-to-string []
  (str-len (int-to-string 42)))

;; Convert a boolean to a string ("true" has length 4)
(defn test-bool-to-string []
  (str-len (bool-to-string true)))

;; Strings in let bindings
(defn test-let-string []
  (let [greeting "hello"
        name     "world"
        msg      (str-concat (str-concat greeting ", ") name)]
    (str-len msg)))

;; Strings passed to and returned from functions
(defn make-greeting [who]
  (str-concat "hello, " who))

(defn test-fn-string []
  (str-len (make-greeting "cranelisp")))

;; Build a string from a number and check its content
(defn test-number-string []
  (if (str-eq (int-to-string 0) "0") 1 0))

;; Expected: 5 + 0 + 11 + 3 + 1 + 0 + 2 + 4 + 12 + 16 + 1 = 55
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-literal-len)
      (add-i64 (test-empty-len)
        (add-i64 (test-concat)
          (add-i64 (test-concat-chain)
            (add-i64 (test-eq-same)
              (add-i64 (test-eq-diff)
                (add-i64 (test-int-to-string)
                  (add-i64 (test-bool-to-string)
                    (add-i64 (test-let-string)
                      (add-i64 (test-fn-string)
                               (test-number-string)))))))))))))
