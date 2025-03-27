; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.

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


; Starting location's are provided and known
(define-fun CoinStartingLocations () Bool
    (and
        (= (LocX Coin_A 0) 0)
        (= (LocY Coin_A 0) 0)

        (= (LocX Coin_B 0) 1)
        (= (LocY Coin_B 0) 0)
    )
)


; Locations need to be bounded to the puzzle area (see ModelingExercises)
; Note: I define the coordinate system to start at 0/0 and to be stricly possitive
(define-fun PuzzleBoundaries () Bool
    (forall ((T Int) (C Int))
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


(define-fun LocationIsEqual ((C1 Int) (C2 Int) (T Int)) Bool
    (and
        (= (LocX C1 T) (LocX C2 T))
        (= (LocY C1 T) (LocY C2 T))
    )
)


(assert 
(and
    CoinIdentifiers
    CoinStartingLocations
    PuzzleBoundaries

    (forall ((T Int) (C1 Int) (C2 Int))
        (and
            ; C1 = C2 => LocationIsEqual
            (implies
                (and
                    (= C1 C2)
                    ; Without clipping T, C1 and C2, this takes forever
                    (>= 0 T)
                    (<= 0 C1 8)
                    (<= 0 C2 8)
                )
                (LocationIsEqual C1 C2 T)
            )
            ; C1 ¬ C2 => ¬ LocationIsEqual
            (implies
                (and
                    (not (= C1 C2))
                    (>= 0 T)
                    (<= 0 C1 8)
                    (<= 0 C2 8)
                )
                (not (LocationIsEqual C1 C2 T))
            )
        )
    )

    ; As time moves from 1 point to the next, a single coin moves to a free location
    (forall ((T1 Int) (T2 Int))
        (implies
            (and
                (= T2 (+ T1 1))
                (< 0 T1 T2)
            )
            (exists ((C Int))
                (and
                    (<= 0 C 8)
                    (or
                        ; Move right
                        (= 
                            (+ (LocX C T1) 1)
                            (LocX C T2)
                        )
                        ; Move left
                        (= 
                            (- (LocX C T1) 1)
                            (LocX C T2)
                        )
                        ; Move up
                        (= 
                            (+ (LocY C T1) 1)
                            (LocY C T2)
                        )
                        ; Move down
                        (= 
                            (- (LocY C T1) 1)
                            (LocY C T2)
                        )
                    )
                )
            )
        )
    )

    ; (exists ((T Int))
    ;     (and
    ;         (= (LocX Coin_A T) 12)
    ;         (= (LocY Coin_A T) 0)
    ;     )
    ; )
    
); End of and
); End of assert

(check-sat)
; (get-model)
(get-value (
    (LocX Coin_A 0)
    (LocY Coin_A 0)
    (LocX Coin_B 0)
    (LocY Coin_B 0)

    (LocX Coin_A 1)
    (LocY Coin_A 1)
    (LocX Coin_B 1)
    (LocY Coin_B 1)

    (LocX Coin_A 2)
    (LocY Coin_A 2)
    (LocX Coin_B 2)
    (LocY Coin_B 2)

    (LocX Coin_A 3)
    (LocY Coin_A 3)
    (LocX Coin_B 3)
    (LocY Coin_B 3)
    
    (LocX Coin_A 4)
    (LocY Coin_A 4)
    (LocX Coin_B 4)
    (LocY Coin_B 4)
    
    (LocX Coin_A 5)
    (LocY Coin_A 5)
    (LocX Coin_B 5)
    (LocY Coin_B 5)
))