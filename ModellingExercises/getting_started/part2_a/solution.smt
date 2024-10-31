(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)
(declare-const N Int)

; Taken from the Modeling Slides:
; "(ite X Y Z)"
; returns Y if X is true, Z otherwise
; (X must be of type Bool)

; in the example above, X is a predicate
; Y and Z should be an int for the problem at hand
; I can utalize the ITE to return 1 for any true values and 0 for any false values
; Then I can add those results up to return the number of true values

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

; Check whether everything works
(push 1)
(assert 
(= (nTrue A B C D) N)
)
(check-sat)
(get-model)
(pop 1)

; N = 4 iff A B C D
(push 2)
(assert
    (and
        (= (nTrue A B C D) N)
        A B C D
        (= N 4)
    )
)
(check-sat)
(get-model)
(pop 2)

; N = 3 if A B C ¬D
(push 3)
(assert
    (and
        (= (nTrue A B C D) N)
        (not D)
        (= N 3)
    )
)
(check-sat)
(get-model)
(pop 3)

; N = 2 if A B ¬C ¬D
(push 4)
(assert
    (and
        (= (nTrue A B C D) N)
        (not C)
        (not D)
        (= N 2)
    )
)
(check-sat)
(get-model)
(pop 4)