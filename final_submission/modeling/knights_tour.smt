; Knight’s Tour (***) 
; Let Z3 find a path for the knight to visit every field on the chess board 
; without ever visiting the same field twice. 

; Position of knight at point in time i is (X i) (Y i)
(declare-fun X (Int) Int)
(declare-fun Y (Int) Int)

(assert (and

; Restrict the knights movement
(forall ((i Int))
    (or
        (and ; right right up
            (= (+ x 2) (X i))
            (= (+ y 1) (Y i))
        )
        (and ; right right down
            (= (+ x 2) (X i))
            (= (- y 1) (Y i))
        )
        (and ; left left up
            (= (- x 2) (X i))
            (= (+ y 1) (Y i))
        )
        (and ; left left down
            (= (- x 2) (X i))
            (= (- y 1) (Y i))
        )
        (and ; right up up
            (= (+ x 1) (X i))
            (= (+ y 2) (Y i))
        )
        (and ; right down down
            (= (+ x 1) (X i))
            (= (- y 2) (Y i))
        )
        (and ; left up up
            (= (- x 1) (X i))
            (= (+ y 2) (Y i))
        )
        (and ; left down down
            (= (- x 1) (X i))
            (= (- y 2) (Y i))
        )
    )
)

)) ; End of assert

(check-sat)
(get-value (
    (X 1)
    (Y 1)
))