(declare-const P Int)
(declare-const Q Int)

(assert (and (= (+ P Q) 37) (= (* P Q) 286)))

(check-sat)
(get-model)