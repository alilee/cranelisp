;; user.cl — Sudoku Solver: the headline end-to-end entry point.
;;
;; This is the showcase story. It wires all four pure modules together and
;; drives them through IO, exactly as the (future) web platform would:
;;
;;   form body  --parse-form-body-->  puzzle string
;;   puzzle     --make-grid-------->  Grid           (the puzzle as entered)
;;   Grid       --solve------------>  SolveResult    (constraint prop + backtrack)
;;   solution   --format-board----->  ASCII board    (terminal view)
;;   solution   --solution-page---->  HTML page      (browser view)
;;
;; Run it:
;;   CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
;;     cargo run -- --run exemplar/user.cl
;;
;; The exemplar is one of the two trees permitted to depend on stdlib
;; (root CLAUDE.md §Stdlib separation).

(platform stdio)
(platform web)

(import [primitives [str-concat int-to-string str-len bind Pure] form [parse-form-body] grid [Grid Cell Given Solved Candidates make-grid is-solved row-of col-of SolveResult Success Unsolvable pow2 bit-set? bit-count cell-at set-cell] solver [solve format-board format-board-str propagate eliminate] html [solution-page] platform.stdio [print]])

(defn cell-char [s idx] (primitives/char-at s idx))

(defn demo-puzzle []
  "003020600900305001001806400008102900700000008006708200002609500800203009005010300")

(defn field-name [idx]
  (let [row (row-of idx) col (col-of idx)]
    (str-concat "c"
      (str-concat (int-to-string row) (int-to-string col)))))

(defn encode-helper [s idx acc]
  (if (= idx 81) acc
    (let
      [ch (cell-char s idx) digit
       (if (= ch "0") "" (if (= ch ".") "" ch))
       sep
       (if (= idx 0) "" "&")
       field
       (str-concat sep
         (str-concat (field-name idx) (str-concat "=" digit)))]
      (encode-helper s (+ idx 1) (str-concat acc field)))))

(defn encode-form-body [s] (encode-helper s 0 ""))

(defn report [puzzle]
  (match (make-grid puzzle)
    [None "Error: invalid puzzle string" (Some g)
     (match (solve g)
       [(Success solution)
        (str-concat "Solution (ASCII):\n"
          (str-concat (format-board solution)
            (str-concat "\n\nSolution (HTML, "
              (str-concat
                (int-to-string (str-len (solution-page solution g)))
                " bytes — ready to serve):\n... <table class=\"sudoku\"> ... </table> ..."))))
        Unsolvable
        "No solution found"])]))

(defn main []
  (let
    [body (encode-form-body (demo-puzzle)) puzzle
     (parse-form-body body)]
    (bind
      (print
        (str-concat "=== Sudoku Solver ===\n\n"
          (str-concat "Parsed "
            (str-concat (int-to-string (str-len body))
              (str-concat "-byte form body into puzzle:\n"
                (str-concat (format-board-str puzzle) "\n\n"))))))
      (fn [_] (print (report puzzle))))))
