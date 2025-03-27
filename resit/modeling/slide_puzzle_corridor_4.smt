; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.


; I define the coordinate system to start at 0/0 and to be stricly possitive, so the red coin starts at 0/0 and needs to move to 0/9


(declare-const Coin_A Int)
(declare-const Coin_B Int)
(declare-const Coin_C Int)
(declare-const Coin_D Int)
(declare-const Coin_E Int)
(declare-const Coin_F Int)
(declare-const Coin_G Int)
(declare-const Coin_H Int)
(declare-const Coin_I Int)
(define-fun CoinIdentifiers () Bool
    (and
        (= Coin_A 0)
        (= Coin_B 1)
        (= Coin_C 2)
        (= Coin_D 3)
        (= Coin_E 4)
        (= Coin_F 5)
        (= Coin_G 6)
        (= Coin_H 7)
        (= Coin_I 8)
    )
)


; Coin's have a location (X / Y) at point in time T
; The first argument of these functions are the coin identifiers, the second is the point in time
(declare-fun LocX (Int Int) Int)
(declare-fun LocY (Int Int) Int)
(declare-const MaxT Int)


; Starting location's are provided and known
(define-fun CoinStartingLocations () Bool
    (and
        (= (LocX Coin_A 0) 0)
        (= (LocY Coin_A 0) 0)

        (= (LocX Coin_B 0) 1)
        (= (LocY Coin_B 0) 0)
        
        (= (LocX Coin_C 0) 2)
        (= (LocY Coin_C 0) 0)

        (= (LocX Coin_D 0) 3)
        (= (LocY Coin_D 0) 0)

        (= (LocX Coin_E 0) 4)
        (= (LocY Coin_E 0) 0)
        
        (= (LocX Coin_F 0) 5)
        (= (LocY Coin_F 0) 0)

        (= (LocX Coin_G 0) 6)
        (= (LocY Coin_G 0) 0)
        
        (= (LocX Coin_H 0) 7)
        (= (LocY Coin_H 0) 0)

        (= (LocX Coin_I 0) 8)
        (= (LocY Coin_I 0) 0)
    )
)


; Locations need to be bounded to the puzzle area (see ModelingExercises)
; Note: I define the coordinate system to start at 0/0 and to be stricly possitive
(define-fun PuzzleBoundaries () Bool
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
)


(define-fun LocationIsEqualToOne ((C1 Int) (C2 Int) (T Int)) Bool
    (and
        (= (LocX C1 T) (LocX C2 T))
        (= (LocY C1 T) (LocY C2 T))
    )
)
(define-fun LocationIsEqualToAny ((C1 Int) (C2 Int) (C3 Int) (C4 Int) (C5 Int) (C6 Int) (C7 Int) (C8 Int) (C9 Int) (T Int)) Bool
    (or
        (LocationIsEqualToOne C1 C2 T)
        (LocationIsEqualToOne C1 C3 T)
        (LocationIsEqualToOne C1 C4 T)
        (LocationIsEqualToOne C1 C5 T)
        (LocationIsEqualToOne C1 C6 T)
        (LocationIsEqualToOne C1 C7 T)
        (LocationIsEqualToOne C1 C8 T)
        (LocationIsEqualToOne C1 C9 T)
    )
)


(assert 
(and
    (= MaxT 20)
    CoinIdentifiers
    CoinStartingLocations
    PuzzleBoundaries

    (forall ((T Int) (C Int))
        (implies
            (and
                (<= 0 T MaxT)
                (<= 0 C 8)
            )
            (=
                ; At point in time T ...
                (LocX C T)
                ; the X value for coin C is equal to ...
                (+
                    ; the value for X at the previous point in time plus ...
                    (LocX C (- T 1)) 
                    ; 1 iff the coin is not:
                    ; - already at the far right, i.e. X at T - 1 < 9
                    ; - in one of the upper spots, i.e. Y at T = 0
                    (ite
                        (and
                            (< (LocX C (- T 1)) 9)
                            (= (LocY C T) 0)
                        )
                        1
                        0
                    )
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
    (LocX Coin_A 4)
    (LocX Coin_A 5)
    (LocX Coin_A 6)
    (LocX Coin_A 7)
    (LocX Coin_A 8)
    (LocX Coin_A 9)
    (LocX Coin_A 10)
    (LocX Coin_A 11)
    true
    (LocX Coin_B 0)
    (LocX Coin_B 1)
    (LocX Coin_B 2)
    (LocX Coin_B 3)
    (LocX Coin_B 4)
    (LocX Coin_B 5)
    (LocX Coin_B 6)
    (LocX Coin_B 7)
    (LocX Coin_B 8)
    (LocX Coin_B 9)
    (LocX Coin_B 10)
    (LocX Coin_B 11)
))