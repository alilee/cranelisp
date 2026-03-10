;; 22-io-hello.cl -- Hello, world with the IO system
;;
;; Cranelisp tracks side effects through the IO type. A function that
;; performs IO returns (IO a) instead of plain a, making effects visible
;; in the type system.
;;
;; This example introduces the core IO primitives:
;;
;;   Pure  -- wrap a value in IO without performing any effect
;;   bind  -- chain IO actions, threading the result of one into the next
;;   print -- a platform function that writes a string to output
;;
;; When main returns (IO a), the runtime trampoline forces the IO tree
;; and extracts the inner value. Effect nodes execute their side effects
;; during forcing. So (Pure 42) as main's return produces 42.
;;
;; Prerequisites:
;;   Build the test-capture platform DLL before running:
;;     cargo build -p cranelisp-test-capture
;;   Run:
;;     cargo run -- --run examples/22-io-hello.cl
;;
;; Note: This example uses the test-capture platform, which captures
;; print output in memory instead of writing to the console. This makes
;; the example verifiable without interactive IO. Replace test-capture
;; with stdio for actual console output.

;; Load the test-capture platform DLL.
(platform test-capture)

;; IO constructors live in `primitives`; print lives in the platform module.
(import [primitives [Pure bind]])
(import [platform.test-capture [print]])


;; === Part 1: Pure -- lifting a value into IO ===

;; Pure wraps any value in IO. No effect occurs.
;; Type: Pure :: (Fn [a] (IO a))

(defn test-pure-value []
  ;; (Pure 42) creates an (IO Int). The trampoline extracts 42.
  (Pure 42))                                         ;; -> 42


;; === Part 2: bind -- chaining IO actions ===

;; bind sequences two IO actions. It takes an IO action and a
;; continuation function. The continuation receives the result of
;; the first action and returns a new IO action.
;; Type: bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))

(defn test-bind-pure []
  ;; Extract 10 from Pure, add 5, wrap in Pure again.
  (bind (Pure 10) (fn [x] (Pure (add-i64 x 5)))))   ;; -> 15

(defn test-bind-chain []
  ;; Chain three steps: start with 1, add 10, add 100.
  (bind (Pure 1)
    (fn [a]
      (bind (Pure (add-i64 a 10))
        (fn [b]
          (Pure (add-i64 b 100)))))))                 ;; -> 111


;; === Part 3: print -- a real side effect ===

;; print takes a String and returns (IO Int). When the trampoline
;; forces the Effect node, the string is written to output.
;; Type: print :: (Fn [String] (IO Int))

(defn test-hello []
  ;; The simplest IO program: print a string.
  ;; Side effect: writes "hello, world" to output.
  (print "hello, world"))                             ;; -> 0

(defn test-print-then-result []
  ;; Print a message, then return a computed value.
  ;; bind sequences the effect and the continuation.
  (bind (print "computing...")
    (fn [_] (Pure 99))))                              ;; -> 99


;; === Part 4: Sequencing two prints ===

;; To print two strings in order, bind the first print's result
;; (which we ignore with _) to a continuation that performs
;; the second print.

(defn test-two-prints []
  ;; Side effects: writes "hello," then "world!" to output.
  (bind (print "hello,")
    (fn [_] (print "world!"))))                       ;; -> 0


;; --- Expected results ---
;;
;; test-pure-value:       42
;; test-bind-pure:        15
;; test-bind-chain:       111
;; test-hello:            0
;; test-print-then-result: 99
;; test-two-prints:       0
;;
;; Total: 42 + 15 + 111 + 0 + 99 + 0 = 267

(defn main []
  (bind (test-pure-value) (fn [r1]
  (bind (test-bind-pure) (fn [r2]
  (bind (test-bind-chain) (fn [r3]
  (bind (test-hello) (fn [r4]
  (bind (test-print-then-result) (fn [r5]
  (bind (test-two-prints) (fn [r6]
    (Pure (add-i64 r1
      (add-i64 r2
        (add-i64 r3
          (add-i64 r4
            (add-i64 r5 r6))))))
  )))))))))))))
