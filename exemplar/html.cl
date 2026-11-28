;; html.cl — HTML generation for the Sudoku solver web interface
;;
;; String construction only; no result type here contains `IO`. Generates:
;; - Form page: 9x9 grid of <input> fields for puzzle entry
;; - Solution page: solved grid as HTML table with given/solved styling
;; - Error page: error message with link back to form
;; - Not-found page: the unknown path with link back to form

(import [collections.vec [range vec-map vec-reduce]])
(import [primitives [str-concat int-to-string contains? replace]])
(import [grid [Grid Given Solved cell-at cell-value]])
(import [testing.assertions [check assert-eq assert-true assert-false]])

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

;; Concatenate `(cell i)` for each i in [0, 9).
(defn nine [cell]
  (vec-reduce (fn [acc i] (str-concat acc (cell i))) "" (range 0 9)))

(defn form-rows []
  (nine (fn [row] (wrap-tag "tr" (nine (fn [col] (input-field row col)))))))

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

(defn solution-rows [original solved]
  (nine
    (fn [row]
      (wrap-tag "tr"
        (nine (fn [col] (solution-cell original solved (+ (* row 9) col))))))))

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

;; ── Not-found page ───────────────────────────────────────────────────

;; Escape text for an HTML element or a double-quoted attribute. `&` goes first
;; so the entities the later replacements insert are not escaped again.
(defn escape-html [text]
  (replace (replace (replace (replace text "&" "&amp;") "<" "&lt;") ">" "&gt;")
    "\"" "&quot;"))

;; The 404 page for an unrecognised method/path. The request path is echoed,
;; escaped, so the caller sees which route missed; the link returns to the form.
(defn not-found-page [path]
  (str-concat "<!DOCTYPE html><html><head><style>"
    (str-concat (css)
      (str-concat "</style><title>Not Found</title></head><body>"
        (str-concat "<h1>404 Not Found</h1><p>No route for <code>"
          (str-concat (escape-html path)
            "</code></p><br><a href=\"/\">Back to the solver</a></body></html>"))))))

;; ── Tests ─────────────────────────────────────────────────────────────
;;
;; Each `test-*` returns `(Option String)`, `None` for a pass
;; (repl/spec/16-test-discovery.md §16.1). `tests.cl` calls them, and
;; `cranelisp --test` discovers them.

(defn test-form-page-has-inputs []
  (assert-true (contains? (form-page) "<td><input type=\"text\" name=\"c88\"")))

(defn test-form-page-has-action []
  (assert-true (contains? (form-page) "<form method=\"POST\" action=\"/solve\">")))

(defn test-form-page-has-table []
  (assert-true (contains? (form-page) "<table class=\"sudoku\">")))

(defn test-wrap-tag []
  (assert-eq "<b>hello</b>" (wrap-tag "b" "hello")))

(defn test-td []
  (assert-eq "<td class=\"given\">5</td>" (td "given" "5")))

(defn test-error-page-has-message []
  (assert-true (contains? (error-page "No solution exists") "<p>No solution exists</p>")))

(defn test-error-page-has-link []
  (assert-true (contains? (error-page "oops") "<a href=\"/\">Try again</a>")))

(defn test-not-found-page-has-path []
  (assert-true (contains? (not-found-page "/nope") "<code>/nope</code>")))

;; A raw client can send any request target, so the echoed path is escaped.
(defn test-not-found-page-escapes-path []
  (let [page (not-found-page "/<script>\"a&b\"</script>")]
    (check
      (assert-false (contains? page "<script>"))
      (assert-true
        (contains? page "/&lt;script&gt;&quot;a&amp;b&quot;&lt;/script&gt;")))))

(defn test-not-found-page-has-link []
  (assert-true (contains? (not-found-page "/x") "<a href=\"/\">Back to the solver</a>")))

;; The page's inline CSS already names `given` and `solved` and contains
;; digits, so these tests assert whole rendered cells.

(defn make-all-ones-grid []
  (Grid (vec-map (fn [_] (Given 1)) (range 0 81))))

;; Cell 0 is Given 5, cell 1 is Solved 3, the rest are Given 1.
(defn make-mixed-grid []
  (Grid
    (vec-map
      (fn [i] (if (= i 0) (Given 5) (if (= i 1) (Solved 3) (Given 1))))
      (range 0 81))))

(defn test-solution-page-has-digits []
  (let [g (make-mixed-grid)
        page (solution-page g g)]
    (check
      (assert-true (contains? page ">5</td>"))
      (assert-true (contains? page ">3</td>")))))

(defn test-solution-page-given-class []
  (let [g (make-all-ones-grid)
        page (solution-page g g)]
    (check
      (assert-true (contains? page "<td class=\"given\">1</td>"))
      (assert-false (contains? page "<td class=\"solved\">")))))

;; The original grid decides the class; the solved grid supplies the digit.
(defn test-solution-page-mixed []
  (let [g (make-mixed-grid)
        page (solution-page g g)]
    (check
      (assert-true (contains? page "<tr><td class=\"given\">5</td><td class=\"solved\">3</td>"))
      (assert-true (contains? page "<td class=\"given\">1</td>")))))
