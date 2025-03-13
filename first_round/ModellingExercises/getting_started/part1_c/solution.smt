(declare-const x1 Real)
(declare-const x2 Real)

(define-fun my_fun ((x Real)) Real
    (+ (+ (* x x) (* 115 x)) 3066)
)

(assert (= (my_fun x1) 0))
(assert (and (= (my_fun x2) 0) (not (= x1 x2))))

(check-sat)
(get-model)