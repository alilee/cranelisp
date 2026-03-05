# Tutorial Curriculum

Section/prompt/trigger/answer definitions for the `/learn` interactive tutorial. See `user/plan-docs.md` for the curriculum overview, design principles, and trigger types.

Each section defines a series of steps. Each step has a prompt (displayed to the student as a comment), a trigger (what constitutes a correct answer), and an answer (the intended solution, shown by `/answer`).

---

## Foundation (Ring 0) -- Sections 1-13

Sections 1-13 cover Ring 0 features: integers, floats, booleans, arithmetic, comparison, let bindings, if expressions, function definitions, calling functions, enum types, pattern matching, and recursion. These sections are deferred to the Ring 0 curriculum pass.

*To be written.*

---

## Data (Ring 1) -- Sections 14-22

### Section 14: `text`

**Teaches**: String literals, string primitives, working with text.

**Prerequisite concepts**: Values and types (section 1-3), calling functions (section 9).

| # | Prompt | Trigger | Answer |
|---|--------|---------|--------|
| 1 | `; type a greeting` | type: String | `"hello"` |
| 2 | `; make an empty string` | value: `""` | `""` |
| 3 | `; how long is "hello"?` | value: 5 | `(str-len "hello")` |
| 4 | `; join "hello" and " world" together` | type: String, value: `"hello world"` | `(str-concat "hello" " world")` |
| 5 | `; are "abc" and "abc" equal?` | value: true | `(str-eq "abc" "abc")` |
| 6 | `; turn the number 42 into a string` | type: String, value: `"42"` | `(int-to-string 42)` |
| 7 | `; what is the length of "hi" joined with " there"?` | value: 8 | `(str-len (str-concat "hi" " there"))` |

**Key concepts introduced**:
- String literals are text in double quotes
- `str-len` measures a string's length
- `str-concat` joins two strings
- `str-eq` compares strings
- `int-to-string`, `float-to-string`, `bool-to-string` convert values to text

---

### Section 15: `data-types`

**Teaches**: Product types -- defining types with fields, constructing values.

**Prerequisite concepts**: Defining enum types (section 10), calling functions (section 9).

| # | Prompt | Trigger | Answer |
|---|--------|---------|--------|
| 1 | `; define a type Point with two Int fields, x and y` | name: Point (type definition exists) | `(deftype Point [:Int x :Int y])` |
| 2 | `; make a Point at 3, 4` | type: Point | `(Point 3 4)` |
| 3 | `; make a Point at the origin (0, 0)` | type: Point | `(Point 0 0)` |
| 4 | `; define a type Triple with three Int fields` | name: Triple (type definition exists) | `(deftype Triple [:Int a :Int b :Int c])` |
| 5 | `; make a Triple with values 10, 20, 30` | type: Triple | `(Triple 10 20 30)` |
| 6 | `; define a type Pair with two fields (no type annotations)` | name: Pair (type definition exists) | `(deftype Pair [first second])` |
| 7 | `; make a Pair of 1 and true` | type: includes Pair | `(Pair 1 true)` |

**Key concepts introduced**:
- `deftype` with a bracketed field list creates a product type
- The type name is also the constructor -- call it like a function
- Fields have `:Type name` syntax for explicit types
- Bare field names get inferred types (polymorphic)

---

### Section 16: `sum-types`

**Teaches**: Sum types -- types with multiple constructors, some carrying data.

**Prerequisite concepts**: Product types (section 15), enum types (section 10).

| # | Prompt | Trigger | Answer |
|---|--------|---------|--------|
| 1 | `; define an Option type: None or Some wrapping a value` | name: Option (type definition exists) | `(deftype (Option a) None (Some [:a val]))` |
| 2 | `; wrap 42 in a Some` | type: includes Option | `(Some 42)` |
| 3 | `; make a None` | type: includes Option | `None` |
| 4 | `; wrap "hello" in a Some` | type: includes Option | `(Some "hello")` |
| 5 | `; define an Either type with Left and Right constructors` | name: Either (type definition exists) | `(deftype (Either a b) (Left [:a val]) (Right [:b val]))` |
| 6 | `; make a Right containing 99` | type: includes Either | `(Right 99)` |

**Key concepts introduced**:
- Sum types have multiple constructors: some nullary, some with fields
- Parenthesized type head `(Option a)` declares a type parameter `a`
- `None` is a nullary constructor (just a name, no data)
- `Some` is a data constructor (wraps a value)
- The same type can be used with different value types (polymorphism)

---

### Section 17: `maybe`

**Teaches**: The Option pattern -- when something might not exist.

**Prerequisite concepts**: Sum types (section 16), pattern matching (section 11).

| # | Prompt | Trigger | Answer |
|---|--------|---------|--------|
| 1 | `; define Option, then write unwrap that returns the value inside Some, or 0 for None` | name: unwrap (function exists with correct type) | `(deftype (Option a) None (Some [:a val])) (defn unwrap [opt] (match opt [(Some x) x None 0]))` |
| 2 | `; unwrap (Some 42)` | value: 42 | `(unwrap (Some 42))` |
| 3 | `; unwrap None` | value: 0 | `(unwrap None)` |
| 4 | `; write is-some that returns 1 for Some and 0 for None` | name: is-some (function exists) | `(defn is-some [opt] (match opt [(Some x) 1 _ 0]))` |
| 5 | `; test is-some on (Some 1)` | value: 1 | `(is-some (Some 1))` |
| 6 | `; test is-some on None` | value: 0 | `(is-some None)` |
| 7 | `; write from-opt that returns the value inside Some, or a default for None` | name: from-opt (function exists) | `(defn from-opt [opt default] (match opt [(Some x) x _ default]))` |

**Key concepts introduced**:
- Option is the standard pattern for "maybe a value"
- `Some` wraps a present value, `None` represents absence
- Pattern matching extracts the value from `Some`
- Common helper functions: unwrap, is-some, from-opt (with default)

---

### Section 18: `matching-data`

**Teaches**: Pattern matching on data constructors with field bindings.

**Prerequisite concepts**: Data types (section 15), sum types (section 16), matching (section 11).

| # | Prompt | Trigger | Answer |
|---|--------|---------|--------|
| 1 | `; define Point, then write get-x that extracts the x field` | name: get-x (function exists) | `(deftype Point [:Int x :Int y]) (defn get-x [p] (match p [(Point a b) a]))` |
| 2 | `; get-x of (Point 7 8)` | value: 7 | `(get-x (Point 7 8))` |
| 3 | `; write sum-point that adds the two fields of a Point` | name: sum-point (function exists) | `(defn sum-point [p] (match p [(Point x y) (add-i64 x y)]))` |
| 4 | `; sum-point of (Point 3 4)` | value: 7 | `(sum-point (Point 3 4))` |
| 5 | `; define Option, then write add-opts that adds two Option Ints (None counts as 0)` | name: add-opts (function exists) | `(deftype (Option a) None (Some [:a val])) (defn add-opts [a b] (match a [None 0 (Some x) (match b [None x (Some y) (add-i64 x y)])]))` |
| 6 | `; add-opts (Some 10) (Some 20)` | value: 30 | `(add-opts (Some 10) (Some 20))` |
| 7 | `; add-opts (Some 5) None` | value: 5 | `(add-opts (Some 5) None)` |

**Key concepts introduced**:
- `(Constructor var1 var2)` patterns bind constructor fields to variables
- Variables in patterns are positional -- they match the field order, not names
- Nested match expressions inspect values within values
- Product types have exactly one constructor, so one pattern suffices

---

### Section 19: `collections`

**Deferred to Sprint 3** (Vec is not in Sprint 2 scope).

---

### Section 20: `lists`

**Deferred to Sprint 3** (List depends on Vec infrastructure).

---

### Section 21: `functions-as-values`

**Teaches**: Closures, lambdas, passing functions as arguments, returning functions.

**Prerequisite concepts**: Defining functions (section 8), let bindings (section 6), calling functions (section 9).

| # | Prompt | Trigger | Answer |
|---|--------|---------|--------|
| 1 | `; make a function that adds 1, and call it on 5 -- all in one expression` | value: 6 | `((fn [x] (add-i64 x 1)) 5)` |
| 2 | `; use let to name a doubling function, then call it on 21` | value: 42 | `(let [f (fn [x] (mul-i64 x 2))] (f 21))` |
| 3 | `; capture n=10, then make a function that adds n to its argument, and call it with 32` | value: 42 | `(let [n 10] ((fn [x] (add-i64 n x)) 32))` |
| 4 | `; write make-adder: takes n, returns a function that adds n` | name: make-adder (function exists) | `(defn make-adder [n] (fn [x] (add-i64 n x)))` |
| 5 | `; use make-adder to make add-ten, then call it on 32` | value: 42 | `((make-adder 10) 32)` |
| 6 | `; write apply-fn that takes a function f and a value x, then calls f on x` | name: apply-fn (function exists) | `(defn apply-fn [f x] (f x))` |
| 7 | `; use apply-fn with a lambda that adds 10, applied to 32` | value: 42 | `(apply-fn (fn [x] (add-i64 x 10)) 32)` |
| 8 | `; pass the named function inc to apply-fn with 41 (define inc first if needed)` | value: 42 | `(defn inc [x] (add-i64 x 1)) (apply-fn inc 41)` |
| 9 | `; write apply-twice: takes f and x, applies f to x twice` | name: apply-twice (function exists) | `(defn apply-twice [f x] (f (f x)))` |
| 10 | `; apply-twice with a function that adds 1, starting from 0` | value: 2 | `(apply-twice (fn [x] (add-i64 x 1)) 0)` |
| 11 | `; write compose: takes f and g, returns a function that applies g then f` | name: compose (function exists) | `(defn compose [f g] (fn [x] (f (g x))))` |
| 12 | `; compose inc and double (where double multiplies by 2), then apply to 5` | value: 11 | `(defn double [x] (mul-i64 x 2)) ((compose inc double) 5)` |

**Key concepts introduced**:
- `(fn [params] body)` creates an anonymous function (closure)
- Closures capture values from their surrounding scope
- Functions can return closures that remember captured values
- Higher-order functions take functions as arguments
- Named functions can be passed as values (no `fn` wrapper needed)
- `compose` and `apply-twice` are common higher-order patterns

---

### Section 22: `map-filter-reduce`

**Deferred to Sprint 3** (depends on Vec/List collections).

---

## Abstraction (Ring 2) -- Sections 23-27

*To be written in Ring 2.*

---

## Meta (Ring 3) -- Sections 28-29

*To be written in Ring 3.*

---

## Effects (Ring 4) -- Sections 30-33

*To be written in Ring 4.*
