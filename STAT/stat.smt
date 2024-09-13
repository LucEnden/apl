(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)

;and ((= (/ 2 (+ A D)) B))
(assert
    (and
        (= (* 2 B) (+ A D))
        (and
            (= (+ (+ A B) (+ C D)) 240)
            (and
                (= (/ (+ A D) 2) B)
                (and
                    (= (+ B D) 60)
                    (and
                        (= (+ A C) 180)
                        (and
                            (= (+ A B) 192)
                            (= (+ C D) 48)
                        )        
                    )
                )
            )
        )
    )
)

(check-sat)
(get-model)