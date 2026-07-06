(import [primitives [add-i64 mul-i64]])

(defn add [a b] (add-i64 a b))

(defn apply-twice [f x] (f (f x)))

(defn double [x] (Num.* x 2))

(defn make-adder [n] (Num.+ n))

(defn mul3 [a b c] (mul-i64 a (mul-i64 b c)))
