(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)

; Functions are borrowed from my solution to part2_a

(define-fun boolToInt ((X Bool)) Int
    (ite X 1 0)
)

(define-fun nTrue ((Af Bool) (Bf Bool) (Cf Bool) (Df Bool)) Int
    (+ 
        (boolToInt Af)
        (boolToInt Bf)
        (boolToInt Cf)
        (boolToInt Df)
    )
)

(assert 
    (= (nTrue A B C D) 1) ; We can view this as a constraint on the domain { A, B, C, D }
)

(check-sat)
(get-model)