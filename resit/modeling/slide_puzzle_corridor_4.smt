; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.

; Definitions:
; - the coordinate system starts at 0/0 and is stricly possitive (so the red coin starts at 0/0 and needs to move to 0/9)


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
            ; I can essentially move this to the assert body, given that the forall and implies signature is the exact same, which might win some performance
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
    (= MaxT 30)
    CoinIdentifiers
    CoinStartingLocations
    PuzzleBoundaries

    ; TODO: implement coin movement, starting with moving coins to the right

    ; The approach used here is to find the location for coin C at the next point in time T
    (forall ((T Int) (C Int))
        (implies
            (and
                (<= 1 T MaxT) ; Start at 1 since possitions at T = 0 are predefined
                (<= 0 C 8)
            )
            (=
                ; At point in time T, the X value for coin C is equal to ...
                (LocX C T)
                (+
                    ; the value for X at the previous point in time plus 1 ...
                    (LocX C (- T 1)) 
                    ; if the coin is:
                    ; 1. not already at the far right, i.e. X at T - 1 < 9
                    ; 2. not in one of the upper spots, i.e. Y at T = 0
                    ; 3. the square it wants to move to is not already occupied, i.e. ... (see not case)
                    (ite
                        (and
                            (< (LocX C (- T 1)) 9)
                            (= (LocY C T) 0)
                            ; (not
                            ;     (forall ((C1 Int) (C2 Int) (C3 Int) (C4 Int) (C5 Int) (C6 Int) (C7 Int) (C8 Int))
                            ;         (and
                            ;             (<= 0 C1 8)
                            ;             (<= 0 C2 8)
                            ;             (<= 0 C3 8)
                            ;             (<= 0 C4 8)
                            ;             (<= 0 C5 8)
                            ;             (<= 0 C6 8)
                            ;             (<= 0 C7 8)
                            ;             (<= 0 C8 8)
                            ;             (distinct C C1 C2 C3 C4 C5 C6 C7 C8)
                            ;             (not (LocationIsEqualToAny C C1 C2 C3 C4 C5 C6 C7 C8 T))
                            ;         )
                            ;     )
                            ; )
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
(get-model)