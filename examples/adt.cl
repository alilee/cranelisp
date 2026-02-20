(platform stdio)
(import [platform.stdio [*]])

;; Algebraic Data Types

;; Product type (struct-like)
(deftype Point [:Int x :Int y])

;; Sum type (tagged union)
(deftype (Option a) None (Some [:a val]))

;; Enum (all-nullary sum type)
(deftype Color Red Green Blue)

;; Shortcut syntax (polymorphic product)
(deftype Pair [first second])

;; Constructor + match
(defn get-x [p]
  (match p
    [(Point px py) px]))

(defn color-value [c]
  (match c
    [Red 1
     Green 2
     Blue 3]))

(defn unwrap-or [opt default]
  (match opt
    [None default
     (Some x) x]))

;; Trait impl for enum ADT
(impl Display Color
  (defn show [c]
    (match c
      [Red "Red"
       Green "Green"
       Blue "Blue"])))

;; Polymorphic trait impl — works for any (Option a) when a has Display
(impl Display (Option :Display a)
  (defn show [self]
    (match self
      [None "None"
       (Some x) (show x)])))

(defn main []
  (do
    (print (show (get-x (Point 3 4))))
    (print (show (color-value Green)))
    (print (show (unwrap-or (Some 42) 0)))
    (print (show (unwrap-or None 99)))
    (print (show Red))
    (print (show (Some 42)))
    (print (show (Some 3.14)))))
