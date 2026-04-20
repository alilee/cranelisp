# Getting Started with Cranelisp

Cranelisp is a programming language. You type instructions, and the computer follows them. Cranelisp checks your instructions for mistakes before running them, so you find problems early. It compiles your code directly to machine instructions so it runs fast.

This guide walks you through installing Cranelisp, starting the interactive prompt, and writing your first programs.

## Installing Cranelisp

You need the Rust toolchain installed. If you do not have it yet, visit [rustup.rs](https://rustup.rs/) and follow the instructions.

Once Rust is installed, clone the Cranelisp repository and build it:

```
git clone https://github.com/alilee/cranelisp
cd cranelisp
cargo build
```

Verify the build succeeded:

```
cargo run -- --help
```

## Starting the REPL

The REPL (Read-Eval-Print Loop) is where you type instructions and see results immediately. Start it by running Cranelisp with no arguments:

```
cargo run
```

You will see a prompt:

```
>
```

This is where you type expressions. After you type something and press Enter, Cranelisp reads what you wrote, checks it, compiles it, runs it, and shows you the result. If something is wrong, it shows you an error message and waits for your next input -- it does not crash.

By default, the REPL uses ANSI colors to syntax-highlight output -- types, values, and errors are styled for readability. To disable colors, pass the `--no-color` flag:

```
cargo run -- --no-color
```

The `NO_COLOR` environment variable is also respected. If `NO_COLOR` is set (to any value), color output is suppressed:

```
NO_COLOR=1 cargo run
```

## Values and Types

Every value in Cranelisp has a **type** -- the kind of thing it is. The REPL shows both the type and the value in its output, using the format `:Type value`.

### Integers

Whole numbers are called `Int`. Type a number at the prompt:

```
> 42
:Int 42
```

The REPL tells you two things: the type is `Int`, and the value is `42`.

Negative numbers work too:

```
> -7
:Int -7
```

And zero:

```
> 0
:Int 0
```

### Booleans

There are exactly two boolean values: `true` and `false`. These represent yes/no, on/off, or any situation with two possibilities.

```
> true
:Bool true

> false
:Bool false
```

### Floats

Decimal numbers are called `Float`. They always contain a decimal point:

```
> 3.14
:Float 3.14

> -0.5
:Float -0.5
```

Integers and floats are different types. `3` is an `Int`, and `3.0` is a `Float`. They cannot be mixed in the same operation.

## Calling Functions

In Cranelisp, you call a function by writing the function name and its arguments inside parentheses:

```
(function-name argument1 argument2)
```

This is different from the `function(argument1, argument2)` notation you might see in a calculator. In Cranelisp, the parentheses go around everything, including the function name, and there are no commas.

### Integer Arithmetic

Cranelisp provides both polymorphic operators like `+` and explicit monomorphic primitives like `add-i64`. The operators dispatch through the trait system — `+` calls `add-i64` for integers and `add-f64` for floats automatically. The explicit primitives are still available when you want to be unambiguous about types.

Cranelisp provides named functions for integer arithmetic:

```
> (add-i64 3 4)
:Int 7

> (sub-i64 10 3)
:Int 7

> (mul-i64 6 7)
:Int 42

> (div-i64 20 4)
:Int 5
```

- `add-i64` adds two integers
- `sub-i64` subtracts the second from the first
- `mul-i64` multiplies two integers
- `div-i64` divides the first by the second (integer division, no remainder). Division by zero causes a runtime panic, as does dividing the minimum integer by -1 (which would overflow)

You can **nest** calls -- use the result of one call as an argument to another:

```
> (add-i64 1 (mul-i64 2 3))
:Int 7
```

Here, `(mul-i64 2 3)` is evaluated first, producing `6`, then `(add-i64 1 6)` produces `7`. The inner expression is always evaluated before the outer one.

You can nest as deeply as you like:

```
> (mul-i64 (add-i64 2 3) (sub-i64 10 4))
:Int 30
```

### Float Arithmetic

Floats have their own set of arithmetic functions. They work the same way as the integer versions, but on decimal numbers:

```
> (add-f64 1.5 2.5)
:Float 4

> (sub-f64 10.0 3.5)
:Float 6.5

> (mul-f64 3.0 4.0)
:Float 12

> (div-f64 10.0 2.0)
:Float 5
```

You cannot mix integers and floats in the same operation. This will produce an error:

```
> (add-i64 1 1.5)
error: type mismatch ...
```

Cranelisp catches this mistake at compile time, before your code runs.

### Comparisons

Comparison functions take two values of the same type and return a `Bool`:

```
> (eq-i64 5 5)
:Bool true

> (eq-i64 5 3)
:Bool false

> (lt-i64 3 5)
:Bool true

> (gt-i64 3 5)
:Bool false

> (le-i64 3 3)
:Bool true

> (ge-i64 5 3)
:Bool true
```

- `eq-i64` -- equal?
- `lt-i64` -- less than?
- `gt-i64` -- greater than?
- `le-i64` -- less than or equal?
- `ge-i64` -- greater than or equal?

Floats have corresponding comparison functions: `eq-f64`, `lt-f64`, `gt-f64`, `le-f64`, `ge-f64`.

### Boolean Logic

The `not` function flips a boolean:

```
> (not true)
:Bool false

> (not false)
:Bool true
```

## Let Bindings

A `let` expression gives names to values. The syntax is:

```
(let [name1 value1 name2 value2 ...] body)
```

The names and values are listed in square brackets, in pairs. The body is an expression that can use those names.

```
> (let [x 10] x)
:Int 10
```

Here, `x` is given the value `10`, and the body is just `x`, which evaluates to `10`.

You can bind multiple names:

```
> (let [x 10 y 20] (add-i64 x y))
:Int 30
```

Later bindings can refer to earlier ones:

```
> (let [x 10 y (add-i64 x 5)] y)
:Int 15
```

You can nest `let` expressions:

```
> (let [x 10 y 20]
    (let [z (add-i64 x y)]
      z))
:Int 30
```

Names introduced by `let` exist only within the body of that `let`. They are temporary.

## If Expressions

The `if` expression chooses between two values based on a condition:

```
(if condition then-value else-value)
```

The condition must be a `Bool`. If it is `true`, the result is the then-value. If it is `false`, the result is the else-value.

```
> (if true 1 2)
:Int 1

> (if false 1 2)
:Int 2

> (if (lt-i64 3 5) 100 200)
:Int 100
```

Both branches must have the same type. This is an error:

```
> (if true 1 true)
error: type mismatch ...
```

You can nest `if` expressions:

```
> (let [n 0]
    (if (lt-i64 n 0)
      -1
      (if (eq-i64 n 0)
        0
        1)))
:Int 0
```

The condition for `if` must be a `Bool`, not a number. This is an error:

```
> (if 1 2 3)
error: type mismatch ...
```

## Defining Functions

The `defn` form defines a named function that you can call later:

```
(defn name [param1 param2 ...] body)
```

The parameters are listed in square brackets. The body is an expression that can use the parameters.

```
> (defn double [x] (mul-i64 x 2))
```

Now you can call it:

```
> (double 5)
:Int 10

> (double 21)
:Int 42
```

Functions can call other functions:

```
> (defn inc [x] (add-i64 x 1))

> (defn double [x] (mul-i64 x 2))

> (double (inc 5))
:Int 12
```

Functions can take multiple parameters:

```
> (defn add3 [a b c] (add-i64 a (add-i64 b c)))

> (add3 1 2 3)
:Int 6
```

### Recursive Functions

A function can call itself. This is called **recursion** -- the function refers to its own name in its body.

Here is a function that counts down from a number to zero:

```
> (defn countdown [n]
    (if (eq-i64 n 0)
      0
      (countdown (sub-i64 n 1))))

> (countdown 5)
:Int 0
```

The classic example is **factorial**: the product of all numbers from 1 to n. Factorial of 5 is 5 times 4 times 3 times 2 times 1, which equals 120.

```
> (defn fact [n]
    (if (eq-i64 n 0)
      1
      (mul-i64 n (fact (sub-i64 n 1)))))

> (fact 5)
:Int 120

> (fact 10)
:Int 3628800
```

Cranelisp optimizes self-recursive functions that call themselves in **tail position** -- meaning the recursive call is the very last thing the function does before returning. This means deeply recursive functions will not run out of memory.

Here is a tail-recursive version of the sum from 1 to n:

```
> (defn sum-acc [n acc]
    (if (eq-i64 n 0)
      acc
      (sum-acc (sub-i64 n 1) (add-i64 acc n))))

> (sum-acc 100 0)
:Int 5050
```

This function passes the running total as a parameter (`acc` for "accumulator") so the recursive call is the last thing evaluated. Cranelisp turns this into a loop internally, so it can handle very large inputs without running out of stack space.

## Type Annotations

Cranelisp infers types automatically -- you rarely need to write them. But you can add type annotations to function parameters to be explicit about what types a function accepts. A type annotation is a colon followed by a type name, placed before the parameter name:

```
(defn inc [:Int x] (add-i64 x 1))
```

This says that `x` must be an `Int`. If you try to pass a different type, Cranelisp catches the error at compile time:

```
> (defn inc [:Int x] (add-i64 x 1))

> (inc 5)
:Int 6

> (inc true)
error: type mismatch ...
```

Type annotations are optional. Without one, Cranelisp figures out the type from how the parameter is used:

```
> (defn double [x] (mul-i64 x 2))
```

Here, Cranelisp infers that `x` must be an `Int` because it is used with `mul-i64`, which requires `Int` arguments.

### Polymorphic Functions

When a function does not constrain the type of a parameter at all, Cranelisp infers that it works with **any** type. This is called **polymorphism** -- one definition works for multiple types.

The simplest example is the identity function, which returns its argument unchanged:

```
> (defn id [x] x)

> (id 42)
:Int 42

> (id true)
:Bool true
```

Cranelisp infers that `id` has type `(Fn [a] a)` -- it takes a value of any type and returns a value of the same type.

## Defining Enum Types

You can define your own types with `deftype`. At this stage, Cranelisp supports **enum types** -- types where the value is one of several named choices, called **constructors**:

```
(deftype TypeName Constructor1 Constructor2 ...)
```

For example, a type representing compass directions:

```
> (deftype Direction North South East West)
```

Each constructor is a value of the new type:

```
> North
:Direction 0

> South
:Direction 1
```

The REPL shows the internal tag number for each constructor. `North` is tag 0, `South` is tag 1, and so on, in the order they are listed.

Here is a type for traffic light colors:

```
> (deftype Light Red Yellow Green)
```

And a type for simple choices:

```
> (deftype Answer Yes No Maybe)
```

Constructor names must start with an uppercase letter.

## Pattern Matching

The `match` expression inspects a value and does different things depending on which constructor it is. The syntax is:

```
(match value
  [Pattern1 result1
   Pattern2 result2
   ...])
```

The patterns and results are listed inside square brackets as alternating pairs. The value is tested against each pattern from top to bottom. The first pattern that matches wins, and its result is evaluated.

```
> (deftype Color Red Green Blue)

> (defn color-val [c]
    (match c
      [Red   1
       Green 2
       Blue  3]))

> (color-val Red)
:Int 1

> (color-val Blue)
:Int 3
```

### Wildcard Patterns

The underscore `_` matches anything. It is useful as a catch-all at the end:

```
> (defn is-red [c]
    (match c
      [Red 1
       _   0]))

> (is-red Red)
:Int 1

> (is-red Green)
:Int 0

> (is-red Blue)
:Int 0
```

### Variable Patterns

A lowercase name in a pattern matches anything and gives it a name you can use in the result:

```
> (deftype Color Red Green Blue)

> (defn to-int [c]
    (match c
      [Red 0
       x   99]))

> (to-int Red)
:Int 0

> (to-int Green)
:Int 99
```

Here, `x` matches any `Color` that is not `Red`. The variable `x` is bound to the matched value, though in this example we do not use it.

### Match with Recursion

Match and recursion work well together. Here is a function that loops using an enum to decide when to stop:

```
> (deftype Action Stop Continue)

> (defn loop-match [n]
    (match (if (eq-i64 n 0) Stop Continue)
      [Stop     0
       Continue (loop-match (sub-i64 n 1))]))

> (loop-match 5)
:Int 0
```

## Running Batch Programs

In addition to the REPL, you can write Cranelisp programs in files and run them directly. Create a file ending in `.cl` -- for example, `factorial.cl`:

```clojure
; factorial.cl -- compute 10 factorial

(defn fact [n]
  (if (eq-i64 n 0)
    1
    (mul-i64 n (fact (sub-i64 n 1)))))

(defn main []
  (fact 10))
```

Run it with:

```
cargo run -- --run factorial.cl
```

In batch mode, Cranelisp compiles and executes the entire file. The program must define a `main` function that takes no parameters. The result of `main` is the program's output.

Lines starting with `;` are **comments** -- they are ignored by the compiler. Use them to explain your code.

### A Batch Program with Multiple Functions

Here is a more complete example. Create a file called `classify.cl`:

```clojure
; classify.cl -- classify a number as negative, zero, or positive

(deftype Sign Negative Zero Positive)

(defn classify [n]
  (if (lt-i64 n 0)
    Negative
    (if (eq-i64 n 0)
      Zero
      Positive)))

(defn sign-to-int [s]
  (match s
    [Negative -1
     Zero      0
     Positive  1]))

(defn main []
  (sign-to-int (classify 42)))
```

Run it:

```
cargo run -- --run classify.cl
```

The result is `1`, because 42 is positive.

## Strings

Strings are text values. They are enclosed in double quotes:

```
> "hello"
:String "hello"

> "world"
:String "world"

> ""
:String ""
```

The REPL shows the type `String` and the text value in quotes.

Strings can contain **escape sequences** for special characters:

```
> "line1\nline2"
:String "line1\nline2"
```

The `\n` inside the string represents a newline character. Other escape sequences are `\t` (tab), `\\` (backslash), and `\"` (a literal double-quote inside a string).

### String Primitives

Cranelisp provides named functions for working with strings:

```
> (str-len "hello")
:Int 5

> (str-len "")
:Int 0
```

`str-len` returns the length of a string as an `Int`.

```
> (str-concat "hello" " world")
:String "hello world"
```

`str-concat` joins two strings together into a new string.

```
> (str-eq "abc" "abc")
:Bool true

> (str-eq "abc" "xyz")
:Bool false
```

`str-eq` compares two strings for equality.

You can convert other types to strings:

```
> (int-to-string 42)
:String "42"

> (float-to-string 3.14)
:String "3.14"

> (bool-to-string true)
:String "true"
```

Strings work with all the features you already know -- `let`, `if`, functions:

```
> (let [greeting "hello"]
    (str-len greeting))
:Int 5

> (defn longer [a b]
    (if (gt-i64 (str-len a) (str-len b)) a b))

> (str-len (longer "hi" "hello"))
:Int 5
```

## Defining Types with Fields

Earlier you saw enum types where each constructor is just a name with no data attached. Now you can define types where constructors carry **fields** -- named pieces of data.

### Product Types

A **product type** is a type with a single constructor that has one or more fields. Think of it as a bundle of values grouped together under one name.

```
(deftype Point [:Int x :Int y])
```

This defines a type called `Point` with two integer fields, `x` and `y`. The type name `Point` also serves as the constructor -- you call it like a function to create values:

```
> (deftype Point [:Int x :Int y])

> (Point 3 4)
:Point (Point 3 4)

> (Point 0 0)
:Point (Point 0 0)
```

Each field has a type annotation (`:Int`) and a name (`x`, `y`). The constructor takes arguments in the same order as the fields.

You can define product types with any number of fields:

```
> (deftype Triple [:Int a :Int b :Int c])

> (Triple 10 20 30)
:Triple (Triple 10 20 30)
```

### Shortcut Syntax

When you do not need to specify the field types, you can use bare field names. Cranelisp will figure out the types from how the values are used:

```
> (deftype Pair [first second])

> (Pair 10 20)
:(Pair Int Int) (Pair 10 20)
```

Here, `Pair` becomes a polymorphic type -- its fields can hold values of any type:

```
> (Pair true false)
:(Pair Bool Bool) (Pair true false)
```

### Sum Types with Data

A **sum type** is a type with multiple constructors. Some constructors can be nullary (no fields), and others can carry data.

The classic example is `Option` -- a type that represents a value that might or might not exist:

```
(deftype (Option a) None (Some [:a val]))
```

This says: an `Option` value is either `None` (nothing is there) or `Some` wrapping a value. The `a` is a type parameter, so `Option` works with any type.

```
> (deftype (Option a) None (Some [:a val]))

> (Some 42)
:(Option Int) (Some 42)

> None
:(Option a) None
```

`None` is a nullary constructor -- it carries no data. `Some` is a data constructor -- it takes one argument.

Here is another sum type with two data constructors:

```
> (deftype (Either a b) (Left [:a val]) (Right [:b val]))

> (Left 42)
:(Either Int b) (Left 42)

> (Right true)
:(Either a Bool) (Right true)
```

And a type where nullary and data constructors are mixed:

```
> (deftype (Result a) Ok (Err [:a val]))

> Ok
:(Result a) Ok

> (Err 404)
:(Result Int) (Err 404)
```

## Pattern Matching on Data Constructors

In the earlier section on pattern matching, you matched against nullary constructors (names with no fields). Now you can match against data constructors too, binding variables to their fields.

### Constructor Patterns with Bindings

A parenthesized pattern matches a data constructor and binds its fields to variables:

```
(match value
  [(ConstructorName var1 var2 ...) result
   ...])
```

The variables bind to the fields by position. You choose the variable names -- they do not need to match the field names from the type definition.

```
> (deftype Point [:Int x :Int y])

> (defn get-x [p]
    (match p [(Point a b) a]))

> (get-x (Point 3 4))
:Int 3

> (defn get-y [p]
    (match p [(Point a b) b]))

> (get-y (Point 3 4))
:Int 4
```

Here, `a` binds to the first field (`x`) and `b` binds to the second field (`y`).

You can compute with the bound variables in the result expression:

```
> (defn sum-point [p]
    (match p [(Point x y) (add-i64 x y)]))

> (sum-point (Point 3 4))
:Int 7
```

### Matching Sum Types

When a type has multiple constructors, the match covers each variant:

```
> (deftype (Option a) None (Some [:a val]))

> (defn unwrap [opt]
    (match opt
      [(Some x) x
       None 0]))

> (unwrap (Some 42))
:Int 42

> (unwrap None)
:Int 0
```

The `(Some x)` pattern matches the `Some` constructor and binds its field to `x`. The `None` pattern matches the nullary constructor.

### Nested Matching

You can nest match expressions to inspect values inside values:

```
> (deftype (Option a) None (Some [:a val]))

> (defn add-opts [a b]
    (match a
      [None 0
       (Some x)
         (match b
           [None x
            (Some y) (add-i64 x y)])]))

> (add-opts (Some 10) (Some 20))
:Int 30

> (add-opts (Some 10) None)
:Int 10

> (add-opts None (Some 5))
:Int 0
```

### Wildcards and Variables Still Work

You can mix constructor patterns with wildcard `_` and variable patterns:

```
> (deftype (Option a) None (Some [:a val]))

> (defn is-some [opt]
    (match opt
      [(Some x) 1
       _ 0]))

> (is-some (Some 42))
:Int 1

> (is-some None)
:Int 0
```

## Closures and Lambdas

A **closure** (also called a **lambda**) is an anonymous function -- a function without a name. You create one with `fn`:

```
(fn [param1 param2 ...] body)
```

The parameters go in square brackets, just like `defn`. The body is an expression.

```
> ((fn [x] (add-i64 x 1)) 5)
:Int 6
```

Here, `(fn [x] (add-i64 x 1))` creates a function that adds 1 to its argument. The outer parentheses call it immediately with the argument `5`.

### Binding Lambdas with Let

You can give a lambda a name using `let`:

```
> (let [f (fn [x] (mul-i64 x 2))]
    (f 21))
:Int 42
```

The variable `f` holds the function. You call it by writing `(f 21)`.

### Capturing Values

The real power of closures is that they can **capture** values from their surrounding scope. When the lambda refers to a name defined outside it, that value is remembered inside the closure:

```
> (let [n 10]
    ((fn [x] (add-i64 n x)) 32))
:Int 42
```

The lambda `(fn [x] (add-i64 n x))` captures the value of `n` (which is `10`). When called with `32`, it computes `10 + 32 = 42`.

Closures can capture multiple values:

```
> (let [a 1 b 2 c 3]
    ((fn [x] (add-i64 a (add-i64 b (add-i64 c x)))) 4))
:Int 10
```

### Returning Closures from Functions

A function can create and return a closure. The returned closure remembers the values that were captured when it was created:

```
> (defn make-adder [n]
    (fn [x] (add-i64 n x)))

> ((make-adder 10) 32)
:Int 42

> ((make-adder 100) 1)
:Int 101
```

`make-adder` takes a number `n` and returns a new function that adds `n` to its argument. Each call to `make-adder` creates a different closure with a different captured value.

## Higher-Order Functions

A **higher-order function** is a function that takes another function as an argument or returns a function as its result. You have already seen `make-adder` returning a function. Now let's pass functions as arguments.

### Passing Functions as Arguments

```
> (defn apply-fn [f x] (f x))

> (apply-fn (fn [x] (add-i64 x 10)) 32)
:Int 42
```

`apply-fn` takes a function `f` and a value `x`, then calls `f` with `x`. You can pass a lambda or a named function:

```
> (defn inc [x] (add-i64 x 1))

> (apply-fn inc 41)
:Int 42
```

Here, the named function `inc` is passed as a value to `apply-fn`.

### Apply Twice

Here is a function that applies a function twice:

```
> (defn apply-twice [f x] (f (f x)))

> (apply-twice (fn [x] (add-i64 x 1)) 0)
:Int 2

> (apply-twice (fn [x] (mul-i64 x 2)) 3)
:Int 12
```

### Compose

Function composition creates a new function from two existing ones:

```
> (defn compose [f g]
    (fn [x] (f (g x))))

> (defn inc [x] (add-i64 x 1))

> (defn double [x] (mul-i64 x 2))

> ((compose inc double) 5)
:Int 11
```

`(compose inc double)` returns a new function that first doubles its argument, then increments the result. So `5 * 2 + 1 = 11`.

### Higher-Order Functions with Recursion

You can combine higher-order functions with recursion to build powerful patterns. Here is a fold that applies a function repeatedly:

```
> (defn fold [f acc n]
    (if (eq-i64 n 0)
      acc
      (fold f (f acc n) (sub-i64 n 1))))

> (fold (fn [acc n] (add-i64 acc n)) 0 100)
:Int 5050
```

This computes the sum of numbers from 1 to 100 by folding with an addition function.

## Vecs -- Growable Arrays

A `Vec` is an ordered, growable collection of values. All elements must have the same type. You create a Vec with square bracket syntax:

```
> [1 2 3]
:(Vec Int) [1 2 3]

> ["hello" "world"]
:(Vec String) ["hello" "world"]

> []
:(Vec a) []
```

The REPL shows the type as `(Vec Int)`, `(Vec String)`, and so on. An empty Vec `[]` has type `(Vec a)` -- the element type is not yet determined.

### Vec Primitives

Cranelisp provides four named functions for working with Vecs:

`vec-len` returns the number of elements:

```
> (vec-len [10 20 30])
:Int 3

> (vec-len [])
:Int 0
```

`vec-get` retrieves an element by index (starting from 0):

```
> (vec-get [10 20 30] 0)
:Int 10

> (vec-get [10 20 30] 2)
:Int 30
```

If the index is out of bounds, the program panics at runtime.

`vec-set` returns a new Vec with one element replaced:

```
> (vec-set [10 20 30] 1 99)
:(Vec Int) [10 99 30]
```

`vec-push` returns a new Vec with an element appended at the end:

```
> (vec-push [10 20] 30)
:(Vec Int) [10 20 30]
```

Both `vec-set` and `vec-push` return **new** Vecs. The original is not modified -- Cranelisp values are immutable. Under the hood, the compiler uses copy-on-write optimization so that when you are the only one holding a reference to the Vec, the update happens in place without copying.

### Vecs Are Polymorphic

A Vec can hold values of any single type. The type is written `(Vec Int)`, `(Vec String)`, `(Vec Bool)`, and so on:

```
> [true false true]
:(Vec Bool) [true false true]

> (vec-push ["a" "b"] "c")
:(Vec String) ["a" "b" "c"]
```

All elements must have the same type. Mixing types is a compile-time error:

```
> [1 true]
error: type mismatch ...
```

### Vecs with Let and Functions

Vecs work with all the features you already know -- `let` bindings, functions, pattern matching:

```
> (let [v [1 2 3]]
    (vec-len v))
:Int 3
```

You can write functions that take and return Vecs:

```
> (defn first-or-zero [v]
    (if (eq-i64 (vec-len v) 0)
      0
      (vec-get v 0)))

> (first-or-zero [10 20 30])
:Int 10

> (first-or-zero [])
:Int 0
```

### Vecs in ADTs

Vecs can appear as fields in your own types:

```
> (deftype Row [:String label :(Vec Int) values])

> (Row "scores" [90 85 92])
:Row (Row "scores" [90 85 92])
```

And you can have Vecs of your own types:

```
> (deftype Color Red Green Blue)

> [Red Green Blue Red]
:(Vec Color) [Red Green Blue Red]
```

### Building Vecs Incrementally

A common pattern is to build a Vec by starting empty and pushing elements in a loop:

```
> (defn count-up [n]
    (defn go [i acc]
      (if (eq-i64 i n)
        acc
        (go (add-i64 i 1) (vec-push acc i))))
    (go 0 []))

> (count-up 5)
:(Vec Int) [0 1 2 3 4]
```

This uses a recursive helper `go` that pushes elements one at a time. Because each `vec-push` is the last use of `acc`, the copy-on-write optimization makes this efficient -- no unnecessary copies.

## Traits

A **trait** describes a shared ability that different types can have. For example, "can be added" is an ability that both integers and floats have, but booleans do not. Traits let you write one function that works with any type that has a particular ability, instead of writing separate functions for each type.

Think of a trait as a contract: "any type that implements this trait promises to support these operations."

### Operators Are Trait Methods

In earlier sections, you used named functions like `add-i64` and `eq-i64` for arithmetic and comparisons. Cranelisp also provides familiar operators like `+`, `-`, `*`, `/`, `=`, and `<`. These operators are **trait methods** -- they work with any type that implements the right trait.

The three core traits are:

- **`Num`** -- numeric operations: `+`, `-`, `*`, `/`
- **`Eq`** -- equality: `=`
- **`Ord`** -- ordering: `<`

Both `Int` and `Float` implement `Num`, so `+` works with either:

```
> (+ 3 4)
:Int 7

> (+ 1.5 2.5)
:Float 4

> (* 6 7)
:Int 42

> (- 10.0 3.5)
:Float 6.5
```

The `=` operator works with `Int`, `Float`, `Bool`, and `String`:

```
> (= 5 5)
:Bool true

> (= 5 3)
:Bool false

> (= "hello" "hello")
:Bool true
```

The `<` operator works with `Int` and `Float`:

```
> (< 3 5)
:Bool true

> (< 5 3)
:Bool false
```

You cannot mix types -- both arguments must be the same type:

```
> (+ 1 1.5)
error: type mismatch ...
```

The named primitives (`add-i64`, `sub-i64`, etc.) still work alongside operators. You can use whichever style you prefer.

### Using Operators in Your Code

You can use operators anywhere you previously used named primitives. Here is the factorial example rewritten with operators:

```
> (defn fact [n]
    (if (= n 0)
      1
      (* n (fact (- n 1)))))

> (fact 5)
:Int 120
```

Compare this to the earlier version that used `eq-i64`, `mul-i64`, and `sub-i64` -- the operator version is shorter and easier to read.

Nesting works the same way:

```
> (+ 1 (* 2 3))
:Int 7
```

### Defining Your Own Traits

You can define your own traits with `deftrait`. A trait declares one or more **methods** -- operations that implementing types must provide.

```
(deftrait TraitName
  (method-name [param-types ...] return-type))
```

The keyword `self` in a method signature is a placeholder for the implementing type. When a type implements the trait, `self` is replaced by that type.

Here is a trait for things that have a numeric size:

```
(deftrait Sizeable
  (size [self] Int))
```

This says: any type that implements `Sizeable` must provide a `size` method that takes a value of that type and returns an `Int`.

### Implementing Traits

You implement a trait for a specific type with `impl`. Inside the `impl`, you define each method using `defn`:

```
(impl TraitName TypeName
  (defn method-name [params ...] body))
```

Here is a complete example:

```clojure
(deftype Shape
  Circle
  Square
  Triangle)

(deftrait Sizeable
  (size [self] Int))

(impl Sizeable Shape
  (defn size [s]
    (match s
      [Circle   1
       Square   4
       Triangle 3])))

(defn main [] (size Square))
```

Running this produces `4` -- a square has 4 sides. The `size` function is called through trait dispatch: Cranelisp looks up the `Sizeable` implementation for `Shape` and calls that version of `size`.

### Multiple Traits

A type can implement multiple traits. Here is a type that implements two different traits:

```clojure
(deftrait Sizeable
  (size [self] Int))

(deftrait Weighable
  (weight [self] Int))

(deftype Animal Cat Dog Bird)

(impl Sizeable Animal
  (defn size [a]
    (match a
      [Cat 3
       Dog 5
       Bird 1])))

(impl Weighable Animal
  (defn weight [a]
    (match a
      [Cat 10
       Dog 25
       Bird 2])))

(defn main []
  (+ (size Dog) (weight Dog)))
```

This produces `30` -- the size of a dog (5) plus the weight of a dog (25).

### Default Methods

When defining a trait, you can provide **default implementations** for some methods. A default method has named parameters and a body, and it is written in terms of other methods from the same trait (or other traits).

The `Ord` trait is a good example. It declares `<` and `>` as required methods, and provides default implementations for `<=` and `>=` that are built from the required methods and `=`:

```clojure
(deftrait Ord
  (< [self self] Bool)
  (> [self self] Bool)
  (<= [x y] Bool (if (< x y) true (= x y)))
  (>= [x y] Bool (if (> x y) true (= x y))))
```

An implementation only needs to provide `<` and `>`. The compiler provides `<=` and `>=` automatically from the defaults. You can use all four comparison operators with `Int` and `Float`:

```
> (> 5 3)
:Bool true

> (<= 3 3)
:Bool true

> (>= 2.0 3.0)
:Bool false
```

When you define your own trait, you can include default methods the same way:

```
(deftrait Describable
  (name [self] String)
  (greeting [x] String (str-concat "Hello, " (name x))))
```

Here, `greeting` has a default implementation that calls `name`. An `impl` block only needs to provide `name` -- `greeting` comes for free.

### Constrained Polymorphism

When you write a function that uses a trait method, Cranelisp automatically infers that the function requires that trait. This is called **constrained polymorphism** -- the function works with any type, as long as that type implements the needed trait.

```
> (defn double [x] (+ x x))
```

Cranelisp infers that `double` requires the `Num` trait, because it uses `+`. You can call it with any numeric type:

```
> (double 5)
:Int 10

> (double 2.5)
:Float 5
```

Behind the scenes, the compiler generates a separate version of `double` for each type you call it with. When you write `(double 5)`, the compiler creates a version specialized for `Int`. When you write `(double 2.5)`, it creates a version specialized for `Float`. This process is called **monomorphisation** -- turning one generic definition into multiple concrete ones. You do not need to do anything special; it happens automatically at each call site.

But you cannot call `double` with a type that does not implement `Num`:

```
> (double true)
error: ...
```

Here is another example -- a generic function constrained by `Ord`:

```
> (defn max-of [a b] (if (> a b) a b))

> (max-of 10 20)
:Int 20

> (max-of 3.14 2.72)
:Float 3.14
```

The compiler infers that `max-of` requires the `Ord` trait because it uses `>`. Each call site gets its own specialized version.

Here is a more involved example -- a function that uses both `Num` and `Eq`:

```clojure
(defn sum-to [n]
  (defn go [i acc]
    (if (= i n)
      acc
      (go (+ i 1) (+ acc i))))
  (go 0 0))

(defn main [] (sum-to 100))
```

This produces `4950` -- the sum of integers from 0 to 99. The function uses `=` (which requires `Eq`) and `+` (which requires `Num`). Cranelisp infers both constraints automatically.

### Type Annotations with Trait Constraints

You already know that type annotations use a colon before a type name, like `:Int`. You can also annotate with a **trait constraint** using the trait name:

```
(defn double [:Num x] (+ x x))
```

This says: `x` can be any type, as long as it implements `Num`. The effect is the same as writing `(defn double [x] (+ x x))` -- Cranelisp would infer the constraint anyway -- but the annotation makes the requirement explicit and serves as documentation.

### Higher-Kinded Traits

The traits you have seen so far operate on concrete types like `Int` or `Shape`. **Higher-kinded traits** operate on type constructors -- types that themselves take a type parameter. This lets you express patterns like "any container that supports mapping over its elements."

The classic example is `Functor`, which describes types that support `fmap` -- applying a function to the value(s) inside a container:

```clojure
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
```

Here, `f` is not a concrete type -- it is a **type constructor** like `Option` or `List`. The trait says: for any type constructor `f`, if you can provide a function from `a` to `b` and a value of type `(f a)`, then `fmap` produces a value of type `(f b)`.

You implement a higher-kinded trait by naming the type constructor (without its type parameter):

```clojure
(impl Functor Option
  (defn fmap [func opt]
    (match opt
      [None       None
       (Some val) (Some (func val))])))
```

Now you can map over `Option` values:

```
> (fmap (fn [x] (+ x 1)) (Some 10))
:(Option Int) (Some 11)

> (fmap (fn [x] (+ x 1)) None)
:(Option Int) None
```

The key difference from regular traits is in the `deftrait` declaration: `(Functor f)` has the type constructor parameter `f` next to the trait name, and the method signatures use `(f a)` to express "the container `f` holding values of type `a`."

### Operators as Values

Trait methods -- including operators like `+`, `-`, `<`, and `=` -- are ordinary values. You can bind them to variables, pass them to higher-order functions, and store them in data structures, just like any other function.

```
> (let [f +] (f 1 2))
:Int 3
```

Here, `+` is bound to the name `f`, and then called through `f`. The compiler wraps the operator in a closure so it can be used wherever a function value is expected.

This is especially useful with higher-order functions. For example, you can pass `+` directly to a fold:

```clojure
(defn fold-vec [v init f]
  (defn go [i acc]
    (if (= i (vec-len v))
      acc
      (go (+ i 1) (f acc (vec-get v i)))))
  (go 0 init))

(defn main []
  (fold-vec [1 2 3 4 5] 0 +))
```

Running this produces `15` -- the sum of all elements, using `+` as the combining function passed to `fold-vec`.

Comparison operators work the same way:

```
> (let [cmp <] (cmp 3 4))
:Bool true
```

Note that constrained polymorphic functions (like a user-defined `(defn add [x y] (+ x y))`) cannot be used as values -- the compiler needs to know the concrete type at the call site in order to generate specialized code. Trait methods like `+` can be used as values because the concrete type is determined where the closure is actually called.

## Putting It Together

You now have all of Ring 0 and Ring 1 at your disposal, plus Vec collections and traits. Here is an example that combines several features -- types with fields, pattern matching, closures, and higher-order functions:

```clojure
; map-option.cl -- transform the value inside an Option

(deftype (Option a) None (Some [:a val]))

(defn map-opt [opt f]
  (match opt
    [(Some x) (Some (f x))
     None None]))

(defn main []
  (match (map-opt (Some 10) (fn [x] (* x 2)))
    [(Some x) x
     None 0]))
```

Running this produces `20` -- the value `10` inside `Some` is doubled by the lambda.

Here is another example combining strings and ADTs:

```clojure
; describe.cl -- convert an Option Int to a descriptive string

(deftype (Option a) None (Some [:a val]))

(defn describe [opt]
  (match opt
    [(Some n) (str-concat "found: " (int-to-string n))
     None "nothing"]))

(defn main []
  (str-len (describe (Some 42))))
```

This produces `9` -- the length of `"found: 42"`.

Here is an example using Vecs with recursion:

```clojure
; sum-vec.cl -- sum all elements of an Int Vec

(defn sum-vec [v]
  (defn go [i acc]
    (if (= i (vec-len v))
      acc
      (go (+ i 1) (+ acc (vec-get v i)))))
  (go 0 0))

(defn main []
  (sum-vec [10 20 30 40]))
```

Running this produces `100` -- the sum of all four elements. The helper function `go` iterates through the Vec by index, accumulating the total. Notice how the operator versions (`=`, `+`) are more readable than the named primitives (`eq-i64`, `add-i64`).

## Summary of Operators and Primitives

### Trait Operators

These operators work with any type that implements the corresponding trait. `Int` and `Float` implement all three core traits. `Bool` and `String` implement `Eq`.

| Operator | Trait | Type | Description |
|----------|-------|------|-------------|
| `+` | `Num` | `(Fn [a a] a)` | Add two values |
| `-` | `Num` | `(Fn [a a] a)` | Subtract second from first |
| `*` | `Num` | `(Fn [a a] a)` | Multiply two values |
| `/` | `Num` | `(Fn [a a] a)` | Divide first by second |
| `=` | `Eq` | `(Fn [a a] Bool)` | Equal? |
| `<` | `Ord` | `(Fn [a a] Bool)` | Less than? |
| `>` | `Ord` | `(Fn [a a] Bool)` | Greater than? |
| `<=` | `Ord` | `(Fn [a a] Bool)` | Less than or equal? (default) |
| `>=` | `Ord` | `(Fn [a a] Bool)` | Greater than or equal? (default) |

### Named Primitives

The named primitives below work with specific types. They are available alongside the trait operators above -- you can use either style:

### Integer Arithmetic and Comparison

| Function | Type | Description |
|----------|------|-------------|
| `add-i64` | `(Fn [Int Int] Int)` | Add two integers |
| `sub-i64` | `(Fn [Int Int] Int)` | Subtract second from first |
| `mul-i64` | `(Fn [Int Int] Int)` | Multiply two integers |
| `div-i64` | `(Fn [Int Int] Int)` | Integer division (panics on zero or overflow) |
| `eq-i64` | `(Fn [Int Int] Bool)` | Equal? |
| `lt-i64` | `(Fn [Int Int] Bool)` | Less than? |
| `gt-i64` | `(Fn [Int Int] Bool)` | Greater than? |
| `le-i64` | `(Fn [Int Int] Bool)` | Less than or equal? |
| `ge-i64` | `(Fn [Int Int] Bool)` | Greater than or equal? |

### Float Arithmetic and Comparison

| Function | Type | Description |
|----------|------|-------------|
| `add-f64` | `(Fn [Float Float] Float)` | Add two floats |
| `sub-f64` | `(Fn [Float Float] Float)` | Subtract second from first |
| `mul-f64` | `(Fn [Float Float] Float)` | Multiply two floats |
| `div-f64` | `(Fn [Float Float] Float)` | Float division |
| `eq-f64` | `(Fn [Float Float] Bool)` | Equal? |
| `lt-f64` | `(Fn [Float Float] Bool)` | Less than? |
| `gt-f64` | `(Fn [Float Float] Bool)` | Greater than? |
| `le-f64` | `(Fn [Float Float] Bool)` | Less than or equal? |
| `ge-f64` | `(Fn [Float Float] Bool)` | Greater than or equal? |

### Boolean

| Function | Type | Description |
|----------|------|-------------|
| `not` | `(Fn [Bool] Bool)` | Negate a boolean |

### String

| Function | Type | Description |
|----------|------|-------------|
| `str-len` | `(Fn [String] Int)` | Length of a string |
| `str-concat` | `(Fn [String String] String)` | Join two strings |
| `str-eq` | `(Fn [String String] Bool)` | Compare two strings for equality |
| `int-to-string` | `(Fn [Int] String)` | Convert integer to string |
| `float-to-string` | `(Fn [Float] String)` | Convert float to string |
| `bool-to-string` | `(Fn [Bool] String)` | Convert boolean to string |

### Vec

| Function | Type | Description |
|----------|------|-------------|
| `vec-len` | `(Fn [(Vec a)] Int)` | Number of elements |
| `vec-get` | `(Fn [(Vec a) Int] a)` | Get element by index (panics if out of bounds) |
| `vec-set` | `(Fn [(Vec a) Int a] (Vec a))` | Return new Vec with element replaced |
| `vec-push` | `(Fn [(Vec a) a] (Vec a))` | Return new Vec with element appended |

## Input and Output

Every program you have written so far has been pure -- it computes a result but does not interact with the outside world. To print text to the screen or read input from the user, you need **IO**.

Cranelisp tracks side effects through the type system. A function that performs IO returns `(IO a)` instead of plain `a`, where `a` is the type of the result. This makes effects visible in the function's type -- you can tell at a glance whether a function is pure or performs IO.

### Why IO is a Type

In many languages, any function can print to the screen or read from the keyboard at any time. In Cranelisp, IO operations return values of type `(IO a)` -- a description of an effect to perform. The effect does not happen immediately. Instead, the runtime collects these descriptions and executes them when the program finishes (or when the REPL displays the result).

This means:

- A function with no `IO` in its return type is guaranteed pure -- it cannot have performed any side effects.
- You can see from a function's type signature whether it does IO.
- IO operations compose predictably using `do` and `bind!` (introduced below).

### Printing with `print`

The `print` function takes a `String` and returns `(IO Int)`. The side effect (writing to the screen) happens when the runtime forces the IO value. The integer result is always `0`.

```
> (print "hello")
hello
:(IO primitives/Int) (IO.Pure 0)
```

The REPL shows two things: first the side effect (`hello` printed to the screen), then the IO result. The type is `(IO primitives/Int)` and the value is displayed as `(IO.Pure 0)` -- the `IO.Pure` wrapper shows that the IO action completed successfully with the inner value `0`.

You can print any string:

```
> (print "hello, world!")
hello, world!
:(IO primitives/Int) (IO.Pure 0)

> (print (int-to-string 42))
42
:(IO primitives/Int) (IO.Pure 0)
```

### Lifting Values with `pure`

The `pure` function wraps any value in IO without performing a side effect:

```
> (pure 42)
:(IO primitives/Int) (IO.Pure 42)

> (pure "hello")
:(IO primitives/String) (IO.Pure "hello")

> (pure true)
:(IO primitives/Bool) (IO.Pure true)
```

Why would you want this? Both branches of an `if` must have the same type. If one branch performs IO, the other must also return an IO type:

```clojure
;; ERROR: one branch is (IO Int), the other is plain Int
(if (> x 0)
  (print (int-to-string x))
  0)

;; OK: both branches return (IO Int)
(if (> x 0)
  (print (int-to-string x))
  (pure 0))
```

### Sequencing with `do`

The `do` macro sequences multiple IO actions. Each action runs in order, and the result of the last action is returned:

```
> (do (print "hello") (print "world"))
hello
world
:(IO primitives/Int) (IO.Pure 0)
```

Every expression inside `do` must have an IO type. Intermediate results are discarded -- `do` is for sequencing effects when you do not need the results of earlier actions.

You can put as many actions as you like inside a `do`:

```
> (do
    (print "one")
    (print "two")
    (print "three"))
one
two
three
:(IO primitives/Int) (IO.Pure 0)
```

### Binding Results with `bind!`

When you need the result of an IO action for use in a later action, use `bind!`. It binds the inner value of an IO action to a name:

```
(bind! [name io-expr
        ...]
  body)
```

Each pair `name io-expr` runs the IO expression, extracts its inner value, and makes it available as `name` in subsequent bindings and the body.

```
> (bind! [x (pure 10)
          y (pure 20)]
    (pure (+ x y)))
:(IO primitives/Int) (IO.Pure 30)
```

Here, `x` gets the value `10` from `(pure 10)`, and `y` gets `20` from `(pure 20)`. The body computes their sum and wraps it in `pure`.

The difference between `do` and `bind!` is simple: `do` discards intermediate results (use it for sequencing effects), while `bind!` names intermediate results (use it when you need them).

### Reading Input with `read-line`

The `read-line` function reads one line of text from the user:

```
read-line :: (Fn [] (IO String))
```

It takes no arguments and returns `(IO String)`. Use `bind!` to get the string value:

```
> (bind! [input (read-line)]
    (print (str-concat "you said: " input)))
```

When this runs, the program waits for you to type a line. After you press Enter, it prints your input back with the prefix "you said: ".

You can chain multiple reads:

```
> (bind! [name (read-line)
          age (read-line)]
    (print (str-concat "hello " (str-concat name (str-concat ", age " age)))))
```

### Automatic IO Scheduling

When you write a `bind!` with multiple independent bindings, the compiler can automatically run them in parallel. Two bindings are independent when neither uses a name defined by the other. The compiler also checks that the platform functions involved are safe to reorder -- functions like `print` must stay in order (you do not want your output lines shuffled), but functions like `http-get` can safely run concurrently because they do not depend on each other's results.

```clojure
;; These two HTTP requests run in parallel automatically
(bind! [response1 (http-get "https://api.example.com/users")
        response2 (http-get "https://api.example.com/posts")]
  (pure (process response1 response2)))
```

The compiler sees that `response1` and `response2` are independent (neither name appears in the other's expression) and that `http-get` is a commutative platform function (safe to reorder). It inserts a parallel node so both requests execute concurrently on a thread pool.

Sequential functions are never reordered:

```clojure
;; These reads stay in order -- read-line is sequential
(bind! [line1 (read-line)
        line2 (read-line)]
  (pure (str-concat line1 line2)))
;; line1 is always the first line read, line2 the second
```

This optimization is semantically transparent -- your program produces the same result whether the compiler parallelizes or not. The only observable difference is speed. To disable automatic IO scheduling (for debugging or profiling), set the environment variable:

```
CRANELISP_NO_IO_SCHEDULE=1 cargo run -- --run myprogram.cl
```

### Platform Declarations

IO operations come from a **platform** -- a library that provides functions like `print` and `read-line`. In batch programs, you declare which platform to use with `(platform stdio)` at the top of the file:

```clojure
(platform stdio)
```

This must appear in the entry module (the file you run), before any platform function calls. The `stdio` platform provides standard console IO.

In the REPL, the platform is loaded automatically when you use platform functions, so you do not need a platform declaration.

### Library Search Path

When Cranelisp loads modules (like the prelude or standard library), it looks for files in specific directories. The compiler resolves the lib directory list using a precedence chain:

1. **Project configuration file** -- `Cranelisp.toml` at the project root (highest precedence below explicit programmatic additions).
2. **`CRANELISP_LIB` environment variable** -- consulted only if no project configuration file is present.
3. **Default fallback** -- `{project_root}/stdlib/`, used only when neither of the above applies.

#### Project Configuration File

Create a `Cranelisp.toml` at your project root to declare lib directories alongside the source. This is the recommended approach for projects that ship their own libraries or live outside the Cranelisp source tree, because the configuration travels with the project under version control.

```toml
# Cranelisp.toml
lib-dirs = ["./vendor/stdlib", "./shared"]
```

Paths in `lib-dirs` may be relative (resolved against the project root) or absolute. When `Cranelisp.toml` is present, its `lib-dirs` list fully replaces the lower precedence tiers -- the `CRANELISP_LIB` environment variable and the default `stdlib/` fallback are not consulted. An empty `lib-dirs = []` (or a missing `lib-dirs` key) is a valid declaration that no lib directories should be searched.

See `spec/08-modules.md` §8.11.4 for the normative precedence rules.

#### Environment Variable

If no `Cranelisp.toml` is present, set `CRANELISP_LIB` to tell the compiler where to find library files:

```
CRANELISP_LIB=/path/to/cranelisp/stdlib cargo run -- --run myproject/main.cl
```

You can specify multiple directories separated by colons:

```
CRANELISP_LIB=/path/to/cranelisp/stdlib:/path/to/my/libs cargo run -- --run main.cl
```

When `CRANELISP_LIB` is set (even to an empty string), the default `stdlib/` fallback is not used -- only the directories you specify are searched. If you set `CRANELISP_LIB=""`, no library directories are searched at all.

### Writing Batch Programs with IO

Batch programs that perform IO must define a `main` function that returns an IO type. The inner value of `main`'s return is used as the program's exit code.

Here is a complete hello-world program. Create a file called `hello.cl`:

```clojure
; hello.cl -- hello world with IO

(platform stdio)
(import [primitives [Pure bind]])
(import [platform.stdio [print]])

(defn main []
  (print "hello, world!"))
```

Run it with:

```
cargo run -- --run hello.cl
```

This prints `hello, world!` to the screen.

Here is a program that sequences multiple prints using `bind`:

```clojure
; greeting.cl -- sequencing IO with bind

(platform stdio)
(import [primitives [Pure bind]])
(import [platform.stdio [print]])

(defn main []
  (bind (print "hello")
    (fn [_]
      (bind (print "world")
        (fn [_] (Pure 0))))))
```

The nested `bind` calls ensure the prints happen in order: first "hello", then "world". The final `(Pure 0)` sets the exit code to 0.

With the prelude loaded, this becomes much simpler using `do`:

```clojure
; greeting.cl -- sequencing IO with do

(platform stdio)
(import [platform.stdio [print]])

(defn main []
  (do
    (print "hello")
    (print "world")
    (pure 0)))
```

The `do` macro handles the bind chaining for you. The `pure` function (lowercase, from the prelude) lifts `0` into IO for the exit code.

### Try It Yourself

1. At the REPL, try `(print "your name here")` and observe both the side effect and the result.

2. Use `do` to print three lines in sequence.

3. Use `bind!` to read a line with `read-line` and print it back with a greeting prefix.

4. Write a batch program that prints a countdown from 3 to "go!":

   ```clojure
   (platform stdio)
   (import [primitives [Pure bind]])
   (import [platform.stdio [print]])

   (defn countdown [n]
     (if (= n 0)
       (print "go!")
       (bind (print (int-to-string n))
         (fn [_] (countdown (- n 1))))))

   (defn main [] (countdown 3))
   ```

   This prints `3`, `2`, `1`, `go!` on separate lines.

For more IO examples, see `examples/21-hello-io.cl` through `examples/24-io-echo.cl` in the repository.

### IO Summary

| Function | Type | Description |
|----------|------|-------------|
| `print` | `(Fn [String] (IO Int))` | Print a string to the screen |
| `read-line` | `(Fn [] (IO String))` | Read one line of text from the user |
| `pure` | `(Fn [a] (IO a))` | Lift a value into IO (no side effect) |
| `bind` | `(Fn [(IO a) (Fn [a] (IO b))] (IO b))` | Chain IO actions (primitive) |
| `do` | macro | Sequence IO actions, discard intermediate results |
| `bind!` | macro | Sequence IO actions, name intermediate results |

## Automatic Parallelism

Cranelisp is a pure functional language -- functions cannot have hidden side effects. The compiler uses this guarantee to automatically parallelize your code in two places: `let` bindings and IO scheduling.

### Lenient Evaluation

When you write a `let` with multiple bindings, the compiler checks whether the bindings depend on each other. If they do not, it evaluates them in parallel automatically.

```
> (let [a (expensive-computation 1)
        b (expensive-computation 2)
        c (expensive-computation 3)]
    (+ a (+ b c)))
```

Here, `a`, `b`, and `c` are independent -- none of them references another. The compiler can evaluate all three concurrently. The result is the same as sequential evaluation, because all three expressions are pure.

A binding is independent if its expression does not mention any name bound earlier in the same `let`. When bindings do depend on each other, the compiler preserves the necessary ordering:

```
> (let [x 10
        y (+ x 5)
        z (+ x 1)]
    (+ y z))
:Int 26
```

Here, `y` depends on `x` and `z` depends on `x`, so `x` must be computed first. But `y` and `z` are independent of each other, so they can be computed in parallel after `x` is ready.

The compiler applies a cost heuristic -- it does not bother parallelizing trivially cheap bindings like arithmetic or variable references, since the overhead of spawning parallel work would outweigh the benefit. Only bindings whose estimated cost exceeds a threshold are candidates.

Lenient evaluation is semantically transparent. Your program behaves the same whether the compiler parallelizes or not. To disable it (for debugging or profiling), set the environment variable:

```
CRANELISP_NO_LENIENT=1 cargo run -- --run myprogram.cl
```

### IO Scheduling

Automatic IO scheduling (described in the IO section above) is the effectful counterpart to lenient evaluation. While lenient evaluation parallelizes pure `let` bindings, IO scheduling parallelizes independent `bind!` bindings that use commutative platform functions. Together, they mean that Cranelisp programs can exploit parallelism without any special syntax or annotations from the programmer.

## Developer Tools

Cranelisp includes several tools to make the development workflow smoother.

### Session Persistence

Your REPL definitions are automatically saved to a `user.cl` file in the current directory. When you restart the REPL, your previous session is restored -- all definitions, imports, and module switches are available immediately.

```
> (defn double [x] (* x 2))
:Int 84
> (double 42)
:Int 84
> /quit

$ cranelisp
> (double 42)
:Int 84
```

The `user.cl` file is a valid Cranelisp source file. You can edit it externally, load it with `--run`, or version-control it alongside your project. To start a completely fresh session, delete `user.cl`.

```
> ;#! cat user.cl
(defn double [x] (* x 2))
```

### Shell Escape

You can run shell commands from the REPL without leaving it. Prefix any shell command with `;#!`:

```
> ;#! ls examples/
01-integers.cl
02-booleans.cl
...

> ;#! wc -l stdlib/prelude.cl
  147 stdlib/prelude.cl
```

The `;` prefix makes the line a comment to the Cranelisp parser, so it never conflicts with valid Cranelisp syntax. The command runs in `/bin/sh` and its output appears directly in the terminal. A non-zero exit code is displayed; a successful command (exit code 0) shows no extra status.

### File Watching

When you are working in the REPL and edit a source file externally, the REPL automatically detects the change and recompiles the affected module. You do not need to manually reload anything.

After each prompt, the REPL checks for file changes. If a file has changed, you see a notification:

```
[updated: core/math.cl]
>
```

If the changed file has errors, the notification tells you:

```
[errors: core/math.cl]
  error: type mismatch at 42..56: expected Int, got Bool
>
```

While a module has errors, evaluation that depends on it is blocked. When you fix the file and save again, the REPL detects the fix, recompiles, and unblocks evaluation.

Cascade invalidation is automatic -- if module A depends on module B and B changes, both B and A are recompiled.

### Building Standalone Executables

To compile a Cranelisp program into a standalone native executable, use the `--link` flag:

```
cranelisp --link myprogram.cl
```

This compiles the module graph, generates a startup stub, and links everything into a native binary. The entry module must define a `main` function that returns either `Int` (exit code) or `IO _` (an IO action).

The `--link` flag uses the module cache -- unchanged modules are not recompiled. The output executable is placed next to the source file with the `.cl` extension removed (e.g., `myprogram.cl` produces `myprogram`).

Requirements:
- macOS aarch64 (Apple Silicon) is currently the only supported target
- The `cranelisp-exe-bundle` library must be built first: `cargo build -p cranelisp-exe-bundle`
- `--link` cannot be combined with `--no-cache` (linking requires cached `.o` files)

### Developer Tools Summary

| Tool | Syntax | Description |
|------|--------|-------------|
| Session persistence | (automatic) | Definitions saved to `user.cl`, restored on restart |
| Shell escape | `;#! <cmd>` | Run a shell command from the REPL |
| File watching | (automatic) | Detect and recompile changed source files |
| `--link` | `cranelisp --link file.cl` | Build a standalone native executable |
| `--no-color` | `cranelisp --no-color` | Disable ANSI color output (also: `NO_COLOR` env var) |
| `CRANELISP_NO_LENIENT` | `CRANELISP_NO_LENIENT=1` | Disable automatic let-binding parallelism |
| `CRANELISP_NO_IO_SCHEDULE` | `CRANELISP_NO_IO_SCHEDULE=1` | Disable automatic IO scheduling parallelism |

## What is Next

This guide covers Ring 0 (core expressions, functions, enums, pattern matching), Ring 1 (strings, data types with fields, closures, higher-order functions, Vec collections), Ring 2A (traits, operators, constrained polymorphism, higher-kinded traits, operators as first-class values), Ring 4 (IO -- reading input, writing output, automatic IO scheduling), automatic parallelism (lenient evaluation, IO scheduling), and developer tools (session persistence, shell escape, file watching, `--link`, `--no-color`). As the language grows, you will gain access to:

- **Modules** -- organizing code across multiple files
- **Macros** -- programs that write programs
- **Lazy sequences** -- the `stdlib/seq/` module provides a `Seq` type for lazy, on-demand sequence processing with producers like `range-from`, `iterate`, and `repeat`, and consumers like `take`, `drop`, `map`, and `filter`

Experiment in the REPL. Try printing and reading input. Write batch programs that combine IO with pattern matching and recursion. Define your own traits and implement them for your types. Use higher-kinded traits like `Functor` to write generic code over containers. The more you experiment, the more fluent you will become.
