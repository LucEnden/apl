
;Assignment:
;   Is 104729 a prime number?  Or 837149927, or 2778545904897799?

;Prime number definition (https://www.cuemath.com/numbers/prime-numbers/)
;   Prime numbers are the numbers that have only two factors, that are, 1 and the number itself.

;Reasoning
;   Any natural number P greater then 1 is considered prime when:
;   P / D = 1 or P / D = P
;   where
;   P > 1 and D > 1
;   

(declare-const P Int)
(declare-const D Int)

(push 1)
(assert
    (and
        (> D 0)
        (> P 1)
        (or
            (= (/ P D) 1)
            (= (/ P D) P)
        )
    )
)

; Id expect this to return the first prime number which I know to be 2, i.e. P = 2
(check-sat)
(get-model)
(pop 1)