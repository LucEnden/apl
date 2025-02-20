;https://www.cuemath.com/numbers/prime-numbers/
;   Any whole number greater than 1 that is divisible only by 1 and itself, is defined as a prime number.
;https://chatgpt.com/share/e3dc57e2-b023-4c17-9e9b-6b734dbb6176
;   In other words, it can't be divided by any other numbers without leaving a remainder.

(declare-const P Int)
(declare-const D Int)

;(define-fun gt1 ((X Int)) Bool
;    (> X 1)
;)
;
;(define-fun divisibleby1oritself ((X Int)) Bool
;    and (= (% X D) 1) (= (% X D) X) 
;)

(assert
    (and
        (> D 0)
        (> 104729 1) 
        (or 
            (= (mod 104729 D) 104729) 
            (= (mod 104729 D) 1)
        )
    )
)
;(assert
;    (and
;        (> D 0)
;        (> P 1) 
;        (or 
;            (= (mod P D) P) 
;            (= (mod P D) 1)
;        )
;    )
;)

(check-sat)
(get-model)