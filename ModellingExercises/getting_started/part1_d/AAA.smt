
;Assignment:
;   Is 104729 a prime number?  Or 837149927, or 2778545904897799?

;Prime number definition (https://www.cuemath.com/numbers/prime-numbers/)
;   Prime numbers are the numbers that have only two factors, that are, 1 and the number itself.

;Reasoning
;   Any natural number P greater then 0 is considered prime when, if we where to divide it by any integer D,
;   i.e. "/ P D" (given that D greater then 0), the product can only by 1 or P

; x/y = z <=> x = yz

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