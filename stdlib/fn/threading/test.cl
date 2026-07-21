;; fn/threading/test.cl — self-tests for fn.threading (module fn.threading.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`.
;;
;; `->` and `->>` are bare-exported by the prelude, so they are among the most
;; visible names in the language and had no coverage at all before S115.
;;
;; The two macros differ ONLY in insertion position, so every case below is
;; written with a NON-COMMUTATIVE operation (`sub-i64`, `str-concat`, a
;; deliberately asymmetric helper). A commutative operation would pass under
;; both macros and prove nothing — the whole point of the pair is that
;; `(-> 1 (sub-i64 10))` and `(->> 1 (sub-i64 10))` must NOT agree.

(import [super [-> ->>]])
(import [testing.assertions [assert-eq assert-true]])
(import [primitives [Option String Int Bool add-i64 sub-i64 mul-i64 str-concat]])

(defn- inc [:Int x] :Int (add-i64 x 1))
(defn- dbl [:Int x] :Int (mul-i64 x 2))

;; ── -> (thread first) ──────────────────────────────────────────────────

(defn test-thread-first-identity [] :(Option String)
  ;; the single-form arity is the identity
  (assert-eq 7 (-> 7)))

(defn test-thread-first-bare-symbol-form [] :(Option String)
  ;; a non-list form becomes a one-argument call
  (assert-eq 8 (-> 7 inc)))

(defn test-thread-first-inserts-as-first-arg [] :(Option String)
  ;; (-> 10 (sub-i64 3)) = (sub-i64 10 3) = 7, NOT (sub-i64 3 10) = -7
  (assert-eq 7 (-> 10 (sub-i64 3))))

(defn test-thread-first-chains-left-to-right [] :(Option String)
  ;; (-> 3 inc dbl) = (dbl (inc 3)) = 8, NOT (inc (dbl 3)) = 7
  (assert-eq 8 (-> 3 inc dbl)))

(defn test-thread-first-mixed-forms [] :(Option String)
  ;; (-> 10 (sub-i64 3) dbl (add-i64 1)) = ((10-3)*2)+1 = 15
  (assert-eq 15 (-> 10 (sub-i64 3) dbl (add-i64 1))))

(defn test-thread-first-on-strings [] :(Option String)
  (assert-eq "ab" (-> "a" (str-concat "b"))))

;; ── ->> (thread last) ──────────────────────────────────────────────────

(defn test-thread-last-identity [] :(Option String)
  (assert-eq 7 (->> 7)))

(defn test-thread-last-bare-symbol-form [] :(Option String)
  (assert-eq 8 (->> 7 inc)))

(defn test-thread-last-inserts-as-last-arg [] :(Option String)
  ;; (->> 3 (sub-i64 10)) = (sub-i64 10 3) = 7, NOT (sub-i64 3 10)
  (assert-eq 7 (->> 3 (sub-i64 10))))

(defn test-thread-last-chains-left-to-right [] :(Option String)
  (assert-eq 8 (->> 3 inc dbl)))

(defn test-thread-last-on-strings [] :(Option String)
  ;; the threaded value lands LAST: (str-concat "b" "a")
  (assert-eq "ba" (->> "a" (str-concat "b"))))

;; ── the pair must DISAGREE ─────────────────────────────────────────────
;;
;; The single case that proves the two macros are not the same macro. If a
;; refactor ever collapses them, every test above still passes and only this
;; one fails.

(defn test-first-and-last-differ-on-noncommutative-op [] :(Option String)
  (assert-true (if (= (-> 3 (sub-i64 10)) (->> 3 (sub-i64 10))) false true)))

(defn test-thread-first-subtracts-in-declared-order [] :(Option String)
  (assert-eq -7 (-> 3 (sub-i64 10))))

(defn test-thread-last-subtracts-in-reversed-order [] :(Option String)
  (assert-eq 7 (->> 3 (sub-i64 10))))
