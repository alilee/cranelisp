;; 21-hello-io.cl -- Introduction to the IO model
;;
;; Cranelisp tracks side effects through the IO type. A function that
;; performs IO returns (IO a) instead of plain a, making effects visible
;; in the type system. The compiler enforces this -- pure functions cannot
;; accidentally perform IO.
;;
;; This example introduces the IO primitives step by step:
;;
;;   1. Pure   -- lift a value into IO (no actual effect)
;;   2. bind   -- chain IO actions, threading values between them
;;   3. Helper combinators built from Pure and bind
;;   4. Platform IO -- actual side effects via (platform stdio), and
;;      why an IO value can be run more than once
;;
;; When main returns (IO a), the runtime's trampoline forces the IO
;; tree and extracts the inner value. So (Pure 42) as main's return
;; produces 42 as the program result. Effect nodes (from platform
;; functions like print) execute their side effects during forcing.
;;
;; Running:
;;   ./target/debug/cranelisp --run examples/21-hello-io.cl
;;
;;   examples/lib/platforms/ ships a stdio.so symlink to cargo's built
;;   libcranelisp_stdio.so, so on Linux the stdio DLL resolves with no
;;   environment variable. On a host without a matching link, set the
;;   search path instead:
;;     CRANELISP_PLATFORM_PATH=target/debug ./target/debug/cranelisp --run …

;; Platform declaration: load the stdio DLL for print/read-line.
;; This must appear before any platform function imports.
(platform stdio)

;; IO constructors and bind live in the `primitives` module.
;; Platform functions live in `platform.stdio`.
(import [primitives [Pure bind]])
(import [platform.stdio [print]])


;; === Part 1: Pure -- lifting values into IO ===

;; Pure wraps any value in an IO context. No effect occurs.
;; Type: Pure :: (Fn [a] (IO a))

(defn check-pure-int []
  ;; (Pure 42) creates an (IO Int) value.
  ;; Roundtrip through bind to prove we can extract the value.
  (bind (Pure 42) (fn [x] (Pure x))))            ;; -> 42

;; Pure works with any type -- Bool, String, etc.
(defn check-pure-bool []
  (bind (Pure true) (fn [b] (Pure (if b 1 0))))) ;; -> 1


;; === Part 2: bind -- chaining IO actions ===

;; bind is the IO sequencing primitive.
;; Type: bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))
;;
;; It takes an IO action and a continuation. The continuation
;; receives the inner value of the first action and returns
;; a new IO action. bind constructs a Bind node in the IO tree;
;; the runtime trampoline evaluates the chain iteratively.

(defn check-bind-simple []
  ;; Extract 10 from (Pure 10), add 5, wrap result in Pure.
  (bind (Pure 10) (fn [x] (Pure (add-i64 x 5)))))  ;; -> 15

(defn check-bind-chain []
  ;; Chain three steps: start with 1, add 10, then add 100.
  (bind (Pure 1)
    (fn [a]
      (bind (Pure (add-i64 a 10))
        (fn [b]
          (Pure (add-i64 b 100)))))))             ;; -> 111

(defn check-bind-multi-ref []
  ;; The continuation can reference earlier bindings (closures).
  ;; Here we bind three values and combine them all at the end.
  (bind (Pure 1)
    (fn [a]
      (bind (Pure 2)
        (fn [b]
          (bind (Pure 3)
            (fn [c]
              (Pure (add-i64 a (add-i64 b c))))))))))  ;; -> 6


;; === Part 3: Conditional IO ===

;; Because IO is a regular type, if-expressions work naturally.
;; Both branches must return the same type -- (IO a) -- so the
;; "do nothing" branch uses Pure to wrap a default value.

(defn check-bind-with-if []
  (bind (Pure 10)
    (fn [x]
      (if (gt-i64 x 5)
        (Pure (add-i64 x 100))                   ;; x > 5: add 100
        (Pure x)))))                              ;; -> 110

(defn check-conditional-io []
  ;; Choose between two IO paths based on a condition.
  (bind (Pure 7)
    (fn [x]
      (bind (if (gt-i64 x 10)
              (Pure (mul-i64 x 2))                ;; big: double
              (Pure (add-i64 x 3)))               ;; small: add 3
        (fn [y]
          (Pure (add-i64 y 1)))))))               ;; -> 11


;; === Part 4: Building combinators from Pure and bind ===
;;
;; The standard library provides combinators like >>, map-io,
;; when-io, etc. Here we build them from scratch to show that
;; Pure and bind are the only primitives you need.

;; then: run two IO actions in sequence, keep the second result.
;; In the standard library this is called `>>`.
(defn then [a b]
  (bind a (fn [_] b)))

(defn check-then []
  ;; (then (Pure 999) (Pure 42)) discards 999, keeps 42.
  (bind (then (Pure 999) (Pure 42))
    (fn [x] (Pure (add-i64 x 8)))))              ;; -> 50

;; map-io: apply a pure function to the result of an IO action.
;; This avoids writing (bind io (fn [x] (Pure (f x)))) everywhere.
(defn map-io [f io-val]
  (bind io-val (fn [x] (Pure (f x)))))

(defn square [n] (mul-i64 n n))

(defn check-map-io []
  ;; map-io square (Pure 5) -> (IO 25), then add 1 -> 26.
  (bind (map-io square (Pure 5))
    (fn [x] (Pure (add-i64 x 1)))))              ;; -> 26


;; === Part 5: Returning IO from helper functions ===

;; Functions that return IO compose naturally with bind.

(defn add-io [x y]
  (Pure (add-i64 x y)))

(defn check-io-helpers []
  (bind (Pure 10)
    (fn [a]
      (bind (Pure 20)
        (fn [b]
          (add-io a b))))))                       ;; -> 30


;; === Part 6: IO with recursion ===

;; Recursive functions can build IO trees. The trampoline
;; evaluates bind chains iteratively, so deep chains don't
;; overflow the call stack.

(defn sum-io [n]
  (if (eq-i64 n 0)
    (Pure 0)
    (bind (sum-io (sub-i64 n 1))
      (fn [rest] (Pure (add-i64 n rest))))))

(defn check-sum-io []
  (sum-io 10))                                   ;; 1+2+...+10 = 55


;; === Part 7: Platform IO -- real side effects ===

;; Now we use the stdio platform to perform actual IO. The `print`
;; function takes a String and returns (IO Int). When the trampoline
;; forces an Effect node, the side effect (writing to stdout) executes.
;;
;; print :: (Fn [String] (IO Int))
;; The return value is 0 (number of bytes is an implementation detail).

(defn check-print-hello []
  ;; The simplest IO program: print a string.
  ;; Side effect: writes "Hello, world!" to stdout.
  (print "Hello, world!"))

(defn check-print-bind []
  ;; Chain two prints with bind. Each print executes in order.
  ;; The continuation receives the result of the previous print
  ;; (always 0) and ignores it with _.
  ;; Side effect: writes "Hello," then "world!" to stdout.
  (bind (print "Hello,")
    (fn [_] (print "world!"))))

(defn check-print-with-result []
  ;; Print a message, then return a computed value.
  ;; bind sequences the effect, then the continuation produces
  ;; a pure result. The trampoline returns the final Pure value.
  ;; Side effect: writes "Computing..." to stdout, returns 42.
  (bind (print "Computing...")
    (fn [_] (Pure 42))))

(defn greet [name]
  ;; Functions that call print inherit the IO return type.
  ;; greet :: (Fn [String] (IO Int))
  ;; IO propagates through the call graph automatically.
  (print name))

(defn check-greet []
  ;; Side effect: writes "Cranelisp" to stdout.
  (greet "Cranelisp"))

(defn check-reuse []
  ;; An IO value describes an effect; it is not the effect itself.
  ;; Naming it with let runs nothing. Each time the value is sequenced,
  ;; its effect runs again, so the same value may be used repeatedly.
  ;; Side effect: writes "again" to stdout twice, then returns 7.
  (let [again (print "again")]
    (bind again (fn [_] (bind again (fn [_] (Pure 7)))))))


;; --- Expected output ---
;;
;; Parts 1-6 (pure computation, no stdout output):
;;   check-pure-int:       42
;;   check-pure-bool:      1
;;   check-bind-simple:    15
;;   check-bind-chain:     111
;;   check-bind-multi-ref: 6
;;   check-bind-with-if:   110
;;   check-conditional-io: 11
;;   check-then:           50
;;   check-map-io:         26
;;   check-io-helpers:     30
;;   check-sum-io:         55
;;   subtotal:            457
;;
;; Part 7 (platform IO, print returns 0):
;;   check-print-hello:       0
;;   check-print-bind:        0
;;   check-print-with-result: 42
;;   check-greet:             0
;;   check-reuse:             7
;;   subtotal:               49
;;
;; Total: 457 + 49 = 506. The exit code is its low byte: 506 mod 256 = 250.
;;
;; Stdout side effects (in execution order):
;;   Hello, world!
;;   Hello,
;;   world!
;;   Computing...
;;   Cranelisp
;;   again
;;   again

(defn main []
  (bind (check-pure-int) (fn [r1]
  (bind (check-pure-bool) (fn [r2]
  (bind (check-bind-simple) (fn [r3]
  (bind (check-bind-chain) (fn [r4]
  (bind (check-bind-multi-ref) (fn [r5]
  (bind (check-bind-with-if) (fn [r6]
  (bind (check-conditional-io) (fn [r7]
  (bind (check-then) (fn [r8]
  (bind (check-map-io) (fn [r9]
  (bind (check-io-helpers) (fn [r10]
  (bind (check-sum-io) (fn [r11]
  ;; Part 7: platform IO tests
  (bind (check-print-hello) (fn [r12]
  (bind (check-print-bind) (fn [r13]
  (bind (check-print-with-result) (fn [r14]
  (bind (check-greet) (fn [r15]
  (bind (check-reuse) (fn [r16]
    (Pure (add-i64 r1
      (add-i64 r2
        (add-i64 r3
          (add-i64 r4
            (add-i64 r5
              (add-i64 r6
                (add-i64 r7
                  (add-i64 r8
                    (add-i64 r9
                      (add-i64 r10
                        (add-i64 r11
                          (add-i64 r12
                            (add-i64 r13
                              (add-i64 r14
                                (add-i64 r15 r16))))))))))))))))
  )))))))))))))))))))))))))))))))))
