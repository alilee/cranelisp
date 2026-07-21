;; 35-ctor-disambiguation.cl -- Same-named constructors across types
;;
;; Builds on 06-enums (deftype + match) and 10-adts (data constructors).
;;
;; Two in-scope types may legitimately share a constructor name:
;;   (deftype Network  (Addr [:Int a]))
;;   (deftype Customer (Addr [:Int a]))
;; Now the bare name `Addr` is AMBIGUOUS -- two constructors in scope
;; answer to it, and the compiler cannot tell which type you mean.
;;
;; The dotted `Type.Ctor` form disambiguates:
;;   - In VALUE position, `Network.Addr` names the Network constructor and
;;     `Customer.Addr` names the Customer one.
;;   - In PATTERN position, the dotted prefix PINS the scrutinee's type:
;;     `(Network.Addr a)` only matches a Network, never a Customer.
;;     A cross-type dotted pattern (matching a Customer against
;;     `(Network.Addr a)`) is a TYPE ERROR, not a runtime miss.
;;
;; The same disambiguation applies to nullary/data variants that collide:
;; here two option-like types both export `Some`, and the dotted form keeps
;; `Maybe.Some` and `Perhaps.Some` apart in both construction and matching.
;;
;; WHERE THE DOT IS NOT ALLOWED — the boundary that makes the rule above
;; unambiguous. `.` qualifies a REFERENCE (a type, a trait, a
;; constructor). It is never part of a BINDER — a name you are
;; introducing. Every one of these is a parse error, uniformly:
;;
;;   (defn a.b [x] x)             ;; the function's own name
;;   (defn f [a.b] a)             ;; a parameter
;;   (let [a.b 1] ...)            ;; a let binding
;;   (match t [(T x.y) x.y])      ;; a pattern variable
;;
;; and each is reported at the offending name:
;;
;;   'a.b' is a dotted name, but a binder must be a bare (unqualified)
;;   name — write 'b' ('.' is reserved for type/trait qualification)
;;
;; Note how this reads against the patterns further down this file. In
;; `(Maybe.Some x)` the dotted `Maybe.Some` is the constructor being
;; REFERRED to; `x` is the name being BOUND, and it is bare. That split —
;; dotted head, bare binder — holds in every pattern in this example.

;; Two option-like types that share the constructor name `Some`.
(deftype (Maybe a)   Nothing (Some [:a val]))
(deftype (Perhaps a) None    (Some [:a val]))

;; Two record-like types that share the constructor name `Addr`.
(deftype Network  (Addr [:Int a]))
(deftype Customer (Addr [:Int a]))

;; Construct via the dotted Type.Ctor form (VALUE position).
;; The bare `Some` / `Addr` would be ambiguous here.
(defn mk-maybe   [] (Maybe.Some 10))
(defn mk-perhaps [] (Perhaps.Some 20))
(defn mk-net     [] (Network.Addr 30))
(defn mk-cust    [] (Customer.Addr 40))

;; Match via the dotted Type.Ctor form (PATTERN position).
;; The dotted prefix pins the scrutinee type: `u-maybe` only accepts a
;; Maybe, `r-net` only a Network. A pattern like `(Customer.Addr a)` in
;; `r-net` would be rejected at compile time as a type mismatch.
(defn u-maybe   [m] (match m [(Maybe.Some x)   x   Nothing 0]))
(defn u-perhaps [p] (match p [(Perhaps.Some x) x   None    0]))
(defn r-net     [n] (match n [(Network.Addr a)  a]))
(defn r-cust    [c] (match c [(Customer.Addr a) a]))

;; Expected: 10 + 20 + 30 + 40 = 100
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (u-maybe (mk-maybe))
      (add-i64 (u-perhaps (mk-perhaps))
        (add-i64 (r-net (mk-net))
                 (r-cust (mk-cust)))))))
