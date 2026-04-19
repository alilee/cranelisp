;; html.cl — HTML generation for the Sudoku solver web interface
;;
;; All pure string manipulation — no IO. Generates:
;; - Form page: 9x9 grid of <input> fields for puzzle entry
;; - Solution page: solved grid as HTML table with given/solved styling
;; - Error page: error message with link back to form
;;
;; Depends on: grid.cl (Grid, Cell, Given, Solved, Candidates, cell-at, cell-value)
;; Depends on: prelude (str macro, cond, do, when, int-to-string, show)

(import [primitives [*]])
(import [grid [Grid Cell Given Solved Candidates cell-at cell-value]])

;; ── CSS ──────────────────────────────────────────────────────────────

;; Inline CSS for Sudoku grid styling.
;; Uses thick borders on every 3rd row/column to delineate 3x3 boxes.
(defn css []
  (str-concat
    (str-concat
      (str-concat
        (str-concat
          "body { font-family: sans-serif; margin: 2em; }"
          " table.sudoku { border-collapse: collapse; }")
        (str-concat
          " table.sudoku td { width: 2em; height: 2em; text-align: center;"
          " border: 1px solid #999; font-size: 1.2em; }"))
      (str-concat
        (str-concat
          " table.sudoku td input { width: 1.5em; height: 1.5em;"
          " text-align: center; border: none; font-size: 1.2em; }")
        (str-concat
          " td.given { font-weight: bold; background: #eee; }"
          " td.solved { color: #0066cc; }")))
    (str-concat
      (str-concat
        " table.sudoku tr:nth-child(3n) td { border-bottom: 2px solid #333; }"
        " table.sudoku tr:first-child td { border-top: 2px solid #333; }")
      (str-concat
        " table.sudoku td:nth-child(3n) { border-right: 2px solid #333; }"
        " table.sudoku td:first-child { border-left: 2px solid #333; }"))))

;; ── Tag helpers ──────────────────────────────────────────────────────

;; Wrap content in an HTML tag: <tag>content</tag>
(defn wrap-tag [tag content]
  (str-concat (str-concat (str-concat "<" tag) ">")
    (str-concat content
      (str-concat (str-concat "</" tag) ">"))))

;; Table cell with CSS class: <td class="cls">content</td>
(defn td [cls content]
  (str-concat
    (str-concat (str-concat "<td class=\"" cls) "\">")
    (str-concat content "</td>")))

;; ── Form page ────────────────────────────────────────────────────────

;; Build a single <input> field for cell at (row, col).
;; Field name is cRC where R=row, C=col (e.g. c00, c35, c88).
(defn input-field [row col]
  (let [name (str-concat "c" (str-concat (int-to-string row) (int-to-string col)))]
    (str-concat
      (str-concat "<td><input type=\"text\" name=\"" name)
      "\" maxlength=\"1\" size=\"1\"></td>")))

;; Build one row of input fields (9 cells).
(defn form-row-helper [row col acc]
  (if (eq-i64 col 9) acc
    (form-row-helper row (add-i64 col 1)
      (str-concat acc (input-field row col)))))

(defn form-row [row]
  (wrap-tag "tr" (form-row-helper row 0 "")))

;; Build all 9 rows of the input grid.
(defn form-rows-helper [row acc]
  (if (eq-i64 row 9) acc
    (form-rows-helper (add-i64 row 1)
      (str-concat acc (form-row row)))))

(defn form-rows []
  (form-rows-helper 0 ""))

;; Full HTML page with puzzle entry form.
(defn form-page []
  (str-concat "<!DOCTYPE html><html><head><style>"
    (str-concat (css)
      (str-concat "</style><title>Sudoku Solver</title></head><body>"
        (str-concat "<h1>Sudoku Solver</h1>"
          (str-concat "<form method=\"POST\" action=\"/solve\">"
            (str-concat "<table class=\"sudoku\">"
              (str-concat (form-rows)
                "</table><br><button type=\"submit\">Solve</button></form></body></html>"))))))))

;; ── Solution page ────────────────────────────────────────────────────

;; Render a single cell of the solution.
;; original is the pre-solve grid — Given cells are styled differently from Solved.
(defn solution-cell [original solved idx]
  (let [orig-cell (cell-at original idx)
        solved-cell (cell-at solved idx)
        digit (int-to-string (cell-value solved-cell))]
    (match orig-cell
      [(Given _) (td "given" digit)
       _ (td "solved" digit)])))

;; Build one row of the solution table (9 cells).
(defn solution-row-helper [original solved row col acc]
  (if (eq-i64 col 9) acc
    (let [idx (add-i64 (mul-i64 row 9) col)]
      (solution-row-helper original solved row (add-i64 col 1)
        (str-concat acc (solution-cell original solved idx))))))

(defn solution-row [original solved row]
  (wrap-tag "tr" (solution-row-helper original solved row 0 "")))

;; Build all 9 rows of the solution table.
(defn solution-rows-helper [original solved row acc]
  (if (eq-i64 row 9) acc
    (solution-rows-helper original solved (add-i64 row 1)
      (str-concat acc (solution-row original solved row)))))

(defn solution-rows [original solved]
  (solution-rows-helper original solved 0 ""))

;; Full HTML page displaying the solved grid.
;; solved: the completed grid.
;; original: the grid as entered (for distinguishing Given vs Solved).
(defn solution-page [solved original]
  (str-concat "<!DOCTYPE html><html><head><style>"
    (str-concat (css)
      (str-concat "</style><title>Solution</title></head><body>"
        (str-concat "<h1>Solution</h1>"
          (str-concat "<table class=\"sudoku\">"
            (str-concat (solution-rows original solved)
              "</table><br><a href=\"/\">Solve another</a></body></html>")))))))

;; ── Error page ───────────────────────────────────────────────────────

;; Display an error message with a link back to the form.
(defn error-page [message]
  (str-concat "<!DOCTYPE html><html><head><style>"
    (str-concat (css)
      (str-concat "</style><title>Error</title></head><body>"
        (str-concat "<h1>Error</h1><p>"
          (str-concat message
            "</p><br><a href=\"/\">Try again</a></body></html>"))))))

;; ── Tests ─────────────────────────────────────────────────────────────
;;
;; Test functions are top-level `test-*` defns returning `(Option String)`
;; per repl/spec.md §16.1. Discoverable via `(discover-tests)`,
;; runnable via `(run-test ...)` — Decision 30 safe pattern (c). No
;; `(mod test ...)` wrapper, no `(import [super [*]])`.

;; Test that form-page contains <input elements
(defn test-form-page-has-inputs []
  (if (contains? (form-page) "<input") None
    (Some "form-page should contain <input elements")))

;; Test that form-page contains form action
(defn test-form-page-has-action []
  (if (contains? (form-page) "/solve") None
    (Some "form-page should contain /solve action")))

;; Test that form-page contains the table
(defn test-form-page-has-table []
  (if (contains? (form-page) "<table") None
    (Some "form-page should contain <table")))

;; Test that wrap-tag works correctly
(defn test-wrap-tag []
  (if (str-eq (wrap-tag "b" "hello") "<b>hello</b>") None
    (Some "wrap-tag should produce <b>hello</b>")))

;; Test that td produces a cell with class
(defn test-td []
  (let [result (td "given" "5")]
    (if (contains? result "given")
      (if (contains? result "5") None
        (Some "td result should contain content '5'"))
      (Some "td result should contain class 'given'"))))

;; Test that error-page contains the error message
(defn test-error-page-has-message []
  (if (contains? (error-page "No solution exists") "No solution exists") None
    (Some "error-page should contain the supplied message")))

;; Test that error-page contains a link back
(defn test-error-page-has-link []
  (if (contains? (error-page "oops") "Try again") None
    (Some "error-page should contain a 'Try again' link")))

;; Helpers for hand-built grids (avoid `let`-recursion patterns).
(defn build-all-ones-helper [v i]
  (if (eq-i64 i 81) v
    (build-all-ones-helper (vec-push v (Given 1)) (add-i64 i 1))))

(defn make-all-ones-grid []
  (Grid (build-all-ones-helper [] 0)))

;; Test that solution-page contains digit strings
(defn test-solution-page-has-digits []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g g) "1") None
      (Some "solution-page should contain digit '1'"))))

;; Test that solution-page has given class for Given cells
(defn test-solution-page-given-class []
  (let [g (make-all-ones-grid)]
    (if (contains? (solution-page g g) "given") None
      (Some "solution-page should contain 'given' CSS class"))))

;; Build a grid where cell 0 is Given(5), cell 1 is Solved(3), the rest are Given(1).
(defn build-mixed-helper [v i]
  (if (eq-i64 i 81) v
    (if (eq-i64 i 0)
      (build-mixed-helper (vec-push v (Given 5)) (add-i64 i 1))
      (if (eq-i64 i 1)
        (build-mixed-helper (vec-push v (Solved 3)) (add-i64 i 1))
        (build-mixed-helper (vec-push v (Given 1)) (add-i64 i 1))))))

(defn make-mixed-grid []
  (Grid (build-mixed-helper [] 0)))

;; Test that solution-page distinguishes Given vs Solved
(defn test-solution-page-mixed []
  (let [g (make-mixed-grid)
        page (solution-page g g)]
    (if (contains? page "given")
      (if (contains? page "solved") None
        (Some "solution-page should contain 'solved' CSS class"))
      (Some "solution-page should contain 'given' CSS class"))))
