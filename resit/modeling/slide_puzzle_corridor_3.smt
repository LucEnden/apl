; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.

(declare-const Coin_A Int)


; Coin's have a location (X / Y) at point in time T
; The first argument of these functions are the coin identifiers, the second is the point in time
(declare-fun LocX (Int Int) Int)
(declare-fun LocY (Int Int) Int)
(declare-const MaxT Int)


(assert 
(and
    (= MaxT 20)

    ; Puzzle Boundaries
    (forall ((T Int) (C Int))
        (implies
            (and
                (<= 0 T MaxT)
                (<= 0 C 8)
            )
            (and
                (<= 0 (LocX C T) 9)
                ; Y can only be 1, if X is either 3, 5 or 7
                (ite
                    (or
                        (= (LocX C T) 3)
                        (= (LocX C T) 5)
                        (= (LocX C T) 7)
                    )
                    ; Y can be 0 or 1
                    (or
                        (= (LocY C T) 0)
                        (= (LocY C T) 1)
                    )
                    ; Y can only be 0
                    (= (LocY C T) 0)
                )
            )
        )
    )
    
    ; Coin identifiers
    (and
        (= Coin_A 0)
    )

    ; Starting positions
    (and
        (= (LocX Coin_A 0) 0)
        (= (LocY Coin_A 0) 0)
    )

    (forall ((T Int))
        (implies
            (<= 1 T 9)
            (=
                (LocX Coin_A T) ; At next point in time
                (+ 
                    (LocX Coin_A (- T 1)) 
                    1 ; Coin moves to the right (possitive X)
                )
            )
        )
    )

); End of and
); End of assert

(check-sat)
; (get-model)
(get-value (
    (LocX Coin_A 0)
    (LocX Coin_A 1)
    (LocX Coin_A 2)
    (LocX Coin_A 3)

    ; (exists ((T Int))
    ;     (and
    ;         (= (LocX Coin_A T) 9)
    ;         (= (LocY Coin_A T) 0)
    ;     )
    ; )
))