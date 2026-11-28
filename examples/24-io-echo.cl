;; 24-io-echo.cl -- Scripted input, transformation and exhaustion
;;
;; 21 sequences output; 22 changes where output goes. Now read-line
;; returns (IO String), and bind supplies the line to the next action.
;; This lesson uses stdio so a shell can supply input without a host API:
;;
;;   printf 'Ada\nLove\nlace\nhello\n' | \
;;     ./target/debug/cranelisp --run examples/24-io-echo.cl
;;
;; Expected stdout: hello, Ada / Lovelace / you said: hello /
;; no input received (one line each). Exit: 4, one per passing check.
;; With closed stdin, all five reads are empty: stdout is hello, / an
;; empty line / no input received / no input received, and exit is 1.
;; read-line returns "" on exhaustion; an empty line has the same value.
;; test-capture (22) instead needs its host to queue input; its queue
;; utilities are not callable Cranelisp platform functions.

(platform stdio)
(import [primitives [pure bind]])
(import [platform.stdio [print read-line]])

;; Transform the first line before writing it. The check observes what
;; was read, rather than adding a constant to an empty string's length.
(defn check-greeting []
  (bind (read-line)
    (fn [name]
      (bind (print (str-concat "hello, " name))
        (fn [_] (pure (if (str-eq name "Ada") 1 0)))))))

;; Nested continuations keep the first line available after the next read.
(defn check-combine []
  (bind (read-line)
    (fn [first]
      (bind (read-line)
        (fn [second]
          (let [joined (str-concat first second)]
            (bind (print joined)
              (fn [_] (pure (if (str-eq joined "Lovelace") 1 0))))))))))

;; Both branches return IO. An empty input does not cause an exception.
(defn respond []
  (bind (read-line)
    (fn [line]
      (if (eq-i64 (str-len line) 0)
        (bind (print "no input received") (fn [_] (pure 0)))
        (bind (print (str-concat "you said: " line))
          (fn [_] (pure 1)))))))

;; Script: greeting=1, combine=1, nonempty response=1, exhausted response=1.
;; Closed stdin: 0 + 0 + 0 + 1 = 1. No prompt or human input is required.
(defn main []
  (bind (check-greeting) (fn [a]
  (bind (check-combine) (fn [b]
  (bind (respond) (fn [c]
  (bind (respond) (fn [empty]
    (pure (add-i64 a (add-i64 b (add-i64 c (if (eq-i64 empty 0) 1 0))))))))))))))
