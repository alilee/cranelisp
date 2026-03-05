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

Cranelisp's arithmetic functions have explicit names like `add-i64` rather than symbols like `+`. This is because the language currently provides monomorphic primitives — each function works with exactly one type. A future version will introduce `+` as a polymorphic operator that automatically selects `add-i64` for integers and `add-f64` for floats. For now, the explicit names make the types unambiguous.

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
- `div-i64` divides the first by the second (integer division, no remainder)

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
cargo run -- factorial.cl
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
cargo run -- classify.cl
```

The result is `1`, because 42 is positive.

## Summary of Ring 0 Primitives

Here is a complete list of the named primitives available:

| Function | Type | Description |
|----------|------|-------------|
| `add-i64` | `(Fn [Int Int] Int)` | Add two integers |
| `sub-i64` | `(Fn [Int Int] Int)` | Subtract second from first |
| `mul-i64` | `(Fn [Int Int] Int)` | Multiply two integers |
| `div-i64` | `(Fn [Int Int] Int)` | Integer division |
| `eq-i64` | `(Fn [Int Int] Bool)` | Equal? |
| `lt-i64` | `(Fn [Int Int] Bool)` | Less than? |
| `gt-i64` | `(Fn [Int Int] Bool)` | Greater than? |
| `le-i64` | `(Fn [Int Int] Bool)` | Less than or equal? |
| `ge-i64` | `(Fn [Int Int] Bool)` | Greater than or equal? |
| `add-f64` | `(Fn [Float Float] Float)` | Add two floats |
| `sub-f64` | `(Fn [Float Float] Float)` | Subtract second from first |
| `mul-f64` | `(Fn [Float Float] Float)` | Multiply two floats |
| `div-f64` | `(Fn [Float Float] Float)` | Float division |
| `eq-f64` | `(Fn [Float Float] Bool)` | Equal? |
| `lt-f64` | `(Fn [Float Float] Bool)` | Less than? |
| `gt-f64` | `(Fn [Float Float] Bool)` | Greater than? |
| `le-f64` | `(Fn [Float Float] Bool)` | Less than or equal? |
| `ge-f64` | `(Fn [Float Float] Bool)` | Greater than or equal? |
| `not` | `(Fn [Bool] Bool)` | Negate a boolean |

## What is Next

This guide covers the core of Cranelisp. As the language grows, you will gain access to:

- **Strings** -- text values like `"hello"`
- **Data types with fields** -- types whose constructors carry data, like `(Some 42)`
- **Closures** -- functions as values that you can pass around
- **Traits** -- shared behavior across types, with operator syntax like `+` and `*`
- **Modules** -- organizing code across multiple files
- **Macros** -- programs that write programs
- **IO** -- reading input and writing output

For now, experiment in the REPL. Try defining your own functions. Write a Fibonacci function. Define an enum type and match on it. The more you experiment, the more fluent you will become.
