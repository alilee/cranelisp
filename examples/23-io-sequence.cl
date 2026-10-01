;; 23-io-sequence.cl -- IO sequencing with bind
;;
;; Example 21 introduced Pure, bind, and print; example 22 showed the
;; test-capture platform. This example focuses on sequencing patterns --
;; how to chain multiple IO actions together when you care about the
;; order of effects.
;;
;; Without a `do` macro (which lives in the standard library), we
;; build sequences using explicit bind calls. This reveals the
;; structure that `do` hides:
;;
;;   (bind action1 (fn [result1]
;;   (bind action2 (fn [result2]
;;     (Pure (use result1 result2))))))
;;
;; Each continuation captures the results of previous actions via
;; closures, so all intermediate values are available at the end.
;;
;; Running:
;;   ./target/debug/cranelisp --run examples/23-io-sequence.cl
;;   (examples/lib/platforms/ ships host-correct symlinks for the
;;    test-capture DLL, so no environment variable is required.)

(platform test-capture)
(import [primitives [Pure bind]])
(import [platform.test-capture [print]])


;; === Part 1: Sequencing with discard ===

;; The simplest sequencing pattern: run an action, ignore its result
;; with _ in the continuation, then run another action.

(defn check-discard []
  ;; Bind discards 999 (via _) and keeps the final 42.
  (bind (Pure 999)
    (fn [_] (Pure 42))))                              ;; -> 42

(defn check-print-sequence []
  ;; Print three lines in order. Each bind discards the previous
  ;; print's result (always 0) and starts the next print.
  ;; Side effects: "one", "two", "three" in order.
  (bind (print "one")
    (fn [_]
      (bind (print "two")
        (fn [_] (print "three"))))))                  ;; -> 0


;; === Part 2: Accumulating results ===

;; When you need the results of multiple IO actions, nest bind calls.
;; Each continuation closes over earlier results.

(defn check-accumulate []
  ;; Bind three pure values and combine them at the end.
  (bind (Pure 10)
    (fn [a]
      (bind (Pure 20)
        (fn [b]
          (bind (Pure 30)
            (fn [c]
              (Pure (add-i64 a (add-i64 b c))))))))))  ;; -> 60


;; === Part 3: Conditional IO ===

;; Both branches of an if-expression must have the same type.
;; When one branch performs IO, the other must also return (IO a).
;; Use Pure to wrap a value in IO without performing an effect.

(defn greet-if-positive [n]
  (if (gt-i64 n 0)
    (bind (print "positive!")
      (fn [_] (Pure n)))
    (Pure n)))

(defn check-conditional-positive []
  ;; n=5 > 0, so print fires. Side effect: "positive!"
  (greet-if-positive 5))                              ;; -> 5

(defn check-conditional-negative []
  ;; n=-1 <= 0, so no print. Pure path only.
  (greet-if-positive (sub-i64 0 1)))                  ;; -> -1


;; === Part 4: map-io -- applying a pure function to IO ===

;; A common pattern: run an IO action, then transform the result
;; with a pure function. We define map-io for this.

(defn map-io [f io-val]
  (bind io-val (fn [x] (Pure (f x)))))

(defn double [n] (mul-i64 n 2))

(defn check-map-io []
  ;; Double the result of a pure IO value.
  (map-io double (Pure 21)))                          ;; -> 42


;; === Part 5: Recursive IO sequences ===

;; IO actions can be built recursively. The trampoline evaluates
;; bind chains iteratively, so deep sequences don't overflow.

(defn print-countdown [n]
  (if (eq-i64 n 0)
    (print "go!")
    (bind (print (int-to-string n))
      (fn [_] (print-countdown (sub-i64 n 1))))))

(defn check-countdown []
  ;; Side effects: "3", "2", "1", "go!" in order.
  (print-countdown 3))                                ;; -> 0


;; === Part 6: IO in helper functions ===

;; Functions that return IO compose naturally with bind.
;; IO propagates through the call graph via type inference.

(defn add-and-announce [a b]
  (let [result (add-i64 a b)]
    (bind (print (int-to-string result))
      (fn [_] (Pure result)))))

(defn check-add-announce []
  ;; Side effect: prints "30".
  (add-and-announce 10 20))                           ;; -> 30


;; --- Expected results ---
;;
;; check-discard:              42
;; check-print-sequence:        0
;; check-accumulate:           60
;; check-conditional-positive:  5
;; check-conditional-negative: -1
;; check-map-io:               42
;; check-countdown:             0
;; check-add-announce:         30
;;
;; Total: 42 + 0 + 60 + 5 + (-1) + 42 + 0 + 30 = 178

(defn main []
  (bind (check-discard) (fn [r1]
  (bind (check-print-sequence) (fn [r2]
  (bind (check-accumulate) (fn [r3]
  (bind (check-conditional-positive) (fn [r4]
  (bind (check-conditional-negative) (fn [r5]
  (bind (check-map-io) (fn [r6]
  (bind (check-countdown) (fn [r7]
  (bind (check-add-announce) (fn [r8]
    (Pure (add-i64 r1
      (add-i64 r2
        (add-i64 r3
          (add-i64 r4
            (add-i64 r5
              (add-i64 r6
                (add-i64 r7 r8))))))))
  )))))))))))))))))
