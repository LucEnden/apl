; Taken from the ModelingExercises.pdf
;   You must spend exactly 400 euro and buy exactly 100 animals. A dog cost 60 euro, a cat 4 
;   euro and a mouse 1 euro each. You have to buy at least one of each. How many of each 
;   should you buy?
(declare-const Nd Int) ; number of dogs
(declare-const Nc Int) ; number of cats
(declare-const Nm Int) ; number of mise

; My reasoning for choosing number of ... here is so I can:
; - multiply these integers by their cost and sum them up to see whether we spend 400 euro.
; - sum these digits to see how many of each we bought

(assert 

(and
    ; The sum of all animals bought should equal 400 exactly
    (= 
        (+
            (* Nd 100)
            (* Nc 4)
            Nm
        )
        400
    )

    ; We need to buy exactly 100 animals
    (=
        (+ Nd Nc Nm)
        100
    )

    ; We need to buy each animal once
    (>= Nd 1)
    (>= Nc 1)
    (>= Nm 1)
)

)

(check-sat)
(get-model)

; Some more notes:
; - after changing the order in which I check how many we bought (+ Nd Nc Nm) and enforce we need to buy each animals once, the model outputed by z3 changes but remains satisfiable
