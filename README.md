## programming language development is dead

I found Claude Code over Xmas and decided I wanted to try to build the programming language that had been on my mind for the last decade or so.

It's a statically-typed, compiled, pure functional lisp, with influences from Carp (strict typing), Roc (purity) and Clojure (syntax and library), and is written in Rust.

The short of it is that I built it in about four weeks part-time - way faster and better than I imagined. With Claude, I am temu Rich Hickey. Before Claude, I had completed the MAL in rust (with difficulty), failed to turn it into a compiler, had only fiddled around in the repl with Carp and Roc, and written some toy web apps in Clojure).

The world does not need another programming language and certainly not another lisp. Programming is dead anyway: "Claude, write it in rust, now write it in python, now 6502 assembly...".

Don't look at my code, because you just build it yourself now: https://github.com/alilee/cranelisp

In terms of process, I was using Opus 4.5 mostly where I was the keeper of ideas, aethestics and helping Claude avoid some terrible design (duplicate data structures mostly).

### Where I got to:
- Statically-typed, pure functional lisp
  ```clojure
     user> (defn inc [x] (+ 1 x))
     inc :: (Fn [Int] Int)
     user> ((+ 1) 1)
     2 :: Int
  ```
- JIT-compiled using cranelift cached in .o files, for instant repl starts, builds and link
- 2-way repl maintains filesystem code and re-compiles external changes
- ADT's
  ```clojure
     (deftype (List a) (Cons a (List a)) Nil)
  ```
- traits:
  ```clojure
     (deftrait (Num a) (+ [a a])) 
     (impl Num Int (defn + [x y] (primitives/add_i64 x y)))
  ```
- HKTs:
  ```clojure
     (deftrait (Functor f) "Mappable container"
       (fmap "Apply function to values inside container" [(Fn [a] b) (f a)] (f b))) 
     (impl Functor Option
       (defn fmap [f opt]
         (match opt
          [None None
          (Some x) (Some (f x))])))
  ```
- loadable platforms (dll for repl and static link for exe)
  ```clojure
     (platform stdio) 
     (import [platform.stdio [print]])
  ```
- discoverable from repl:
  ```clojure
     user> print
     platform.stdio/print :: platform primitive: (Fn [String] (IO Int))
     user> /info print
     platform.stdio/print :: platform primitive
       (defn platform.stdio/print "Print a string" [:String s] (IO Int))
  ```
- compiled macros from repl that use full language:
 ```clojure
    (defmacro const- "Define a private named constant" [name value]
      `(defmacro- ~name [] ~(quote-sexp value)))
    user> /expand (const PI 3.14)
    (defmacro PI [] (SexpFloat 3.14))
    user> PI
    3.14 :: Float
 ```
- 31k rust LOC
- what's next? concurrency, llvm, Roc-style platform; until I get bored and Claude and I start writing an operating system for it.
