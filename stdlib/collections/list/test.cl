;; collections/list/test.cl — self-tests for collections.list (module
;; collections.list.test)
;;
;; Separate backing file (extraction-stable per spec §8.2.5). Parent declares
;; `(mod- test)`. The operation tests reduce list values to Int/Bool first
;; (length/empty?/fold); the trait-impl tests compare lists themselves.

(import [super [List Nil Cons empty? length first rest fold reverse
                map-list filter-list nth]])
(import [testing.assertions [assert-true assert-false assert-eq]])
(import [compare.eq [= !=]])
(import [compare.ord [< > <= >=]])
(import [text.display [show]])
(import [primitives [Option Some None String Int add-i64 eq-i64]])

(defn- l123 [] :(List Int) (Cons 1 (Cons 2 (Cons 3 Nil))))

(defn test-empty-nil [] :(Option String)
  (assert-true (empty? :(List Int) Nil)))

(defn test-not-empty [] :(Option String)
  (assert-false (empty? (l123))))

(defn test-length [] :(Option String)
  (assert-eq 3 (length (l123))))

(defn test-fold-sum [] :(Option String)
  (assert-eq 6 (fold (fn [acc x] (add-i64 acc x)) 0 (l123))))

(defn test-reverse-length [] :(Option String)
  (assert-eq 3 (length (reverse (l123)))))

(defn test-first-some [] :(Option String)
  (match (first (l123))
    [(Some h) (if (eq-i64 h 1) None (Some "first wrong"))
     None     (Some "expected Some")]))

(defn test-map-list-length [] :(Option String)
  (assert-eq 3 (length (map-list (fn [x] (add-i64 x 1)) (l123)))))

;; ── Trait impls ──────────────────────────────────────────────────────

(defn test-eq-same-elements [] :(Option String)
  (assert-true (= (l123) (Cons 1 (Cons 2 (Cons 3 Nil))))))

(defn test-eq-element-differs [] :(Option String)
  (assert-true (!= (l123) (Cons 1 (Cons 9 (Cons 3 Nil))))))

(defn test-eq-prefix-is-not-equal [] :(Option String)
  (assert-false (= (Cons 1 (Cons 2 Nil)) (l123))))

(defn test-eq-nested [] :(Option String)
  (assert-eq (Cons (Cons 1 Nil) Nil) (Cons (Cons 1 Nil) Nil)))

(defn test-ord-prefix-is-less [] :(Option String)
  (assert-true (< (Cons 1 (Cons 2 Nil)) (l123))))

(defn test-ord-longer-is-not-less [] :(Option String)
  (assert-false (< (l123) (Cons 1 (Cons 2 Nil)))))

(defn test-ord-element-decides-before-length [] :(Option String)
  (assert-true (> (Cons 2 Nil) (l123))))

(defn test-ord-equal-is-not-lt [] :(Option String)
  (assert-false (< (l123) (l123))))

(defn test-ord-le-ge-when-equal [] :(Option String)
  (assert-true (if (<= (l123) (l123)) (>= (l123) (l123)) false)))

(defn test-ord-empty-is-least [] :(Option String)
  (assert-true (< Nil (l123))))

(defn test-show-list [] :(Option String)
  (assert-eq "(1 2 3)" (show (l123))))

(defn test-show-empty [] :(Option String)
  (assert-eq "()" (show :(List Int) Nil)))

(defn test-show-nested [] :(Option String)
  (assert-eq "((1) ())" (show (Cons (Cons 1 Nil) (Cons Nil Nil)))))
