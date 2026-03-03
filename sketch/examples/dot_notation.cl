(platform stdio)
(import [platform.stdio [*]])

;; Dot notation: Type.Constructor and Trait.method

(defn unwrap-or [opt default]
  (match opt
    [Option.None default
     (Option.Some x) x]))

(defn main []
  (do
    ;; Type.Constructor — data constructor call
    (print (show (unwrap-or (Option.Some 42) 0)))

    ;; Type.Constructor — nullary constructor
    (print (show (unwrap-or Option.None 99)))

    ;; Trait.method — operator via trait
    (print (show (Num.+ 1 2)))

    ;; Trait.method — regular method
    (print (Display.show 7))

    ;; Pattern matching with dotted constructors
    (print (show (match (Option.Some 5)
                   [(Option.Some v) v
                    Option.None 0])))))
