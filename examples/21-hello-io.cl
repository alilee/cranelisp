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
;;   4. Platform IO -- actual side effects via (platform stdio)
;;
;; When main returns (IO a), the runtime's trampoline forces the IO
;; tree and extracts the inner value. So (Pure 42) as main's return
;; produces 42 as the program result. Effect nodes (from platform
;; functions like print) execute their side effects during forcing.
;;
;; Running:
;;   Use the justfile recipe, which builds the platform cdylibs and puts
;;   target/debug on the platform search path so the stdio DLL resolves:
;;     just run-example examples/21-hello-io.cl
;;
;;   The recipe sets CRANELISP_PLATFORM_PATH=target/debug; discovery then
;;   finds cargo's libcranelisp_stdio.{so,dylib,dll} directly (no symlinks).

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

(defn test-pure-int []
  ;; (Pure 42) creates an (IO Int) value.
  ;; Roundtrip through bind to prove we can extract the value.
  (bind (Pure 42) (fn [x] (Pure x))))            ;; -> 42

;; Pure works with any type -- Bool, String, etc.
(defn test-pure-bool []
  (bind (Pure true) (fn [b] (Pure (if b 1 0))))) ;; -> 1


;; === Part 2: bind -- chaining IO actions ===

;; bind is the IO sequencing primitive.
;; Type: bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))
;;
;; It takes an IO action and a continuation. The continuation
;; receives the inner value of the first action and returns
;; a new IO action. bind constructs a Bind node in the IO tree;
;; the runtime trampoline evaluates the chain iteratively.

(defn test-bind-simple []
  ;; Extract 10 from (Pure 10), add 5, wrap result in Pure.
  (bind (Pure 10) (fn [x] (Pure (add-i64 x 5)))))  ;; -> 15

(defn test-bind-chain []
  ;; Chain three steps: start with 1, add 10, then add 100.
  (bind (Pure 1)
    (fn [a]
      (bind (Pure (add-i64 a 10))
        (fn [b]
          (Pure (add-i64 b 100)))))))             ;; -> 111

(defn test-bind-multi-ref []
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

(defn test-bind-with-if []
  (bind (Pure 10)
    (fn [x]
      (if (gt-i64 x 5)
        (Pure (add-i64 x 100))                   ;; x > 5: add 100
        (Pure x)))))                              ;; -> 110

(defn test-conditional-io []
  ;; Choose between two IO paths based on a condition.
  (bind (Pure 7)
    (fn [x]
      (bind (if (gt-i64 x 10)
              (Pure (mul-i64 x 2))                ;; big: double
              (Pure (add-i64 x 3)))               ;; small: add 3
        (fn [y]
          (Pure (add-i64 y 1)))))))               ;; -> 11


;; === Part 4: Building combinators from Pure and bind ===

;; The standard library provides combinators like >>, map-io,
;; when-io, etc. Here we build them from scratch to show that
;; Pure and bind are the only primitives you need.

;; then: run two IO actions in sequence, keep the second result.
;; In the standard library this is called `>>`.
(defn then [a b]
  (bind a (fn [_] b)))

(defn test-then []
  ;; (then (Pure 999) (Pure 42)) discards 999, keeps 42.
  (bind (then (Pure 999) (Pure 42))
    (fn [x] (Pure (add-i64 x 8)))))              ;; -> 50

;; map-io: apply a pure function to the result of an IO action.
;; This avoids writing (bind io (fn [x] (Pure (f x)))) everywhere.
(defn map-io [f io-val]
  (bind io-val (fn [x] (Pure (f x)))))

(defn square [n] (mul-i64 n n))

(defn test-map-io []
  ;; map-io square (Pure 5) -> (IO 25), then add 1 -> 26.
  (bind (map-io square (Pure 5))
    (fn [x] (Pure (add-i64 x 1)))))              ;; -> 26


;; === Part 5: Returning IO from helper functions ===

;; Functions that return IO compose naturally with bind.

(defn add-io [x y]
  (Pure (add-i64 x y)))

(defn test-io-helpers []
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

(defn test-sum-io []
  (sum-io 10))                                   ;; 1+2+...+10 = 55


;; === Part 7: Platform IO -- real side effects ===

;; Now we use the stdio platform to perform actual IO. The `print`
;; function takes a String and returns (IO Int). When the trampoline
;; forces an Effect node, the side effect (writing to stdout) executes.
;;
;; print :: (Fn [String] (IO Int))
;; The return value is 0 (number of bytes is an implementation detail).

(defn test-print-hello []
  ;; The simplest IO program: print a string.
  ;; Side effect: writes "Hello, world!" to stdout.
  (print "Hello, world!"))

(defn test-print-bind []
  ;; Chain two prints with bind. Each print executes in order.
  ;; The continuation receives the result of the previous print
  ;; (always 0) and ignores it with _.
  ;; Side effect: writes "Hello," then "world!" to stdout.
  (bind (print "Hello,")
    (fn [_] (print "world!"))))

(defn test-print-with-result []
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

(defn test-greet []
  ;; Side effect: writes "Cranelisp" to stdout.
  (greet "Cranelisp"))


;; --- Expected output ---
;;
;; Parts 1-6 (pure computation, no stdout output):
;;   test-pure-int:       42
;;   test-pure-bool:      1
;;   test-bind-simple:    15
;;   test-bind-chain:     111
;;   test-bind-multi-ref: 6
;;   test-bind-with-if:   110
;;   test-conditional-io: 11
;;   test-then:           50
;;   test-map-io:         26
;;   test-io-helpers:     30
;;   test-sum-io:         55
;;   subtotal:            457
;;
;; Part 7 (platform IO, print returns 0):
;;   test-print-hello:       0
;;   test-print-bind:        0
;;   test-print-with-result: 42
;;   test-greet:             0
;;   subtotal:               42
;;
;; Total: 457 + 42 = 499
;;
;; Stdout side effects (in execution order):
;;   Hello, world!
;;   Hello,
;;   world!
;;   Computing...
;;   Cranelisp

(defn main []
  (bind (test-pure-int) (fn [r1]
  (bind (test-pure-bool) (fn [r2]
  (bind (test-bind-simple) (fn [r3]
  (bind (test-bind-chain) (fn [r4]
  (bind (test-bind-multi-ref) (fn [r5]
  (bind (test-bind-with-if) (fn [r6]
  (bind (test-conditional-io) (fn [r7]
  (bind (test-then) (fn [r8]
  (bind (test-map-io) (fn [r9]
  (bind (test-io-helpers) (fn [r10]
  (bind (test-sum-io) (fn [r11]
  ;; Part 7: platform IO tests
  (bind (test-print-hello) (fn [r12]
  (bind (test-print-bind) (fn [r13]
  (bind (test-print-with-result) (fn [r14]
  (bind (test-greet) (fn [r15]
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
                              (add-i64 r14 r15)))))))))))))))
  )))))))))))))))))))))))))))))))
