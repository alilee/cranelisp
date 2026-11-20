;; smoke.cl — quick smoke test for the solver: solves a fixed puzzle and prints
;; the input board and its solution. The headline showcase is `user.cl`.
;;
;; Run it:
;;   CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
;;     cargo run -- --run exemplar/smoke.cl

(platform stdio)

(import [primitives [str-concat bind]])
(import [grid [make-grid Success Unsolvable]])
(import [solver [solve format-board format-board-str]])
(import [platform.stdio [print]])

;; Solve a fixed puzzle and print the input board, then the solution.
(defn main []
  (let [puzzle "003020600900305001001806400008102900700000008006708200002609500800203009005010300"]
    (bind (print (str-concat "=== Sudoku Solver ===\n\nPuzzle:\n"
                   (format-board-str puzzle)))
      (fn [_]
        (match (make-grid puzzle)
          [None (print "\nError: invalid puzzle string")
           (Some g)
             (match (solve g)
               [(Success solution)
                  (print (str-concat "\nSolution:\n" (format-board solution)))
                Unsolvable
                  (print "\nNo solution found")])])))))
