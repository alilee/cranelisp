;; user.cl — Sudoku Solver: the headline end-to-end entry point.
;;
;; It drives the core modules along the same path as the web entry's `/solve`
;; route (`main.cl`):
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

(platform stdio)

(import [primitives [str-concat int-to-string str-len char-at]])
(import [collections.vec [range vec-reduce]])
(import [text.string [char-to-digit]])
(import [platform.stdio [print]])
(import [form [parse-form-body]])
(import [grid [make-grid row-of col-of Success Unsolvable]])
(import [solver [solve format-board format-board-str]])
(import [html [solution-page]])

(defn demo-puzzle []
  "003020600900305001001806400008102900700000008006708200002609500800203009005010300")

;; The form field of cell `idx`: `cRC` for row R and column C.
(defn field-name [idx]
  (str-concat "c"
    (str-concat (int-to-string (row-of idx)) (int-to-string (col-of idx)))))

;; The URL-encoded body the form page submits for `puzzle`: one `cRC=d` field
;; per cell, with an empty value for an empty cell (`0` or `.`).
(defn encode-form-body [puzzle]
  (vec-reduce
    (fn [body idx]
      (let [ch (char-at puzzle idx)
            digit (if (< (char-to-digit ch) 1) "" ch)
            sep (if (= idx 0) "" "&")]
        (str-concat body
          (str-concat sep (str-concat (field-name idx) (str-concat "=" digit))))))
    ""
    (range 0 81)))

(defn report [puzzle]
  (match (make-grid puzzle)
    [None "Error: invalid puzzle string"
     (Some g)
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
  (let [body (encode-form-body (demo-puzzle))
        puzzle (parse-form-body body)]
    (do
      (print
        (str-concat "=== Sudoku Solver ===\n\nParsed "
          (str-concat (int-to-string (str-len body))
            (str-concat "-byte form body into puzzle:\n"
              (str-concat (format-board-str puzzle) "\n\n")))))
      (print (report puzzle)))))
