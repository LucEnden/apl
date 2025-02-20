
;Assignment:
;   Is 104729 a prime number?  Or 837149927, or 2778545904897799?

;Prime number definition (https://www.cuemath.com/numbers/prime-numbers/)
;   Prime numbers are the numbers that have only two factors, that are, 1 and the number itself.
;https://chatgpt.com/share/e3dc57e2-b023-4c17-9e9b-6b734dbb6176
;   In other words, it can't be divided by any other numbers without leaving a remainder.

;Reasoning
;   Any natural number P greater then 0 is considered prime when, if we where to divide it by any integer D,
;   i.e. "/ P D" (given that D greater then 0), the product can only by 1 or P

;   After recieving feedback from Herman about the fact that division results are reals,
;   I needed to look into how to translate the "/ P D" formula into one that uses multiplication

;   x/y = z <=> x = yz
;   Let P equal a number we want to check if it is prime
;   Let D > 1 <= P
;   Let R be the result
;   P/D = R <=> P = DR

;   P = 2, D = 2, R = 2/2 = 1
;   OR 
;   R = 2, D = 2, P = 2*2 = 4

;   P = 3
;   D = 2
;   R = 3/2 = 

(declare-const P Int)
(declare-const D Int)
(declare-const N Int)

; (push 1)
; (assert
;     (and
;         (> D 0)
;         (> P 1)
;         (or
;             (= (/ P D) 1)
;             (= (/ P D) P)
;         )
;     )
; )

; ; Id expect this to return the first prime number which I know to be 2, i.e. P = 2
; (check-sat)
; (get-model)
; (pop 1)

(push 2)
(assert
    (and
        (> D 0)
        (> P 1)
        (or
            (= (* D N) P)
        )
    )
)

; Id expect this to return the first prime number which I know to be 2, i.e. P = 2
(check-sat)
(get-model)
(pop 2)

(push 3)
(assert
    (and
        (> D 0)
        (= P 4)
        (or
            (= (* D N) P)
        )
    )
)

; Id expect this to return the first prime number which I know to be 2, i.e. P = 2
(check-sat)
(get-model)
(pop 3)

(push 4)
(assert
    (and
        (> D 0)
        (= P 104729)
        (or
            (= (* D N) P)
        )
    )
)

; Id expect this to return the first prime number which I know to be 2, i.e. P = 2
(check-sat)
(get-model)
(pop 4)