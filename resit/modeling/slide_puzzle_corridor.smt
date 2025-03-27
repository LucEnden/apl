; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.

; Square's will be identified simply by their coordinate points (X/Y, both starting at 0 and going positivly up)
; Coin identifiers are as bellow (these are there starting possitions):
; |   |   |   |   |   |   |   |   |   |   | 
; | A | B | C | D | E | F | G | H | I |   |
(declare-const Coin_A Int)
(declare-const Coin_B Int)
(declare-const Coin_C Int)
(declare-const Coin_D Int)
(declare-const Coin_E Int)
(declare-const Coin_F Int)
(declare-const Coin_G Int)
(declare-const Coin_H Int)
(declare-const Coin_I Int)

; Coin's have a location (X / Y) at point in time T
; The first argument of these functions are the coin identifiers, the second is the point in time
(declare-fun Coin_Location_X (Int Int) Int)
(declare-fun Coin_Location_Y (Int Int) Int)

(define-fun Coin_Constrains () Bool
    (and
        ; Coin identification, no need for distinct
        (= Coin_A 0)
        (= Coin_B 1)
        (= Coin_C 2)
        (= Coin_D 3)
        (= Coin_E 4)
        (= Coin_F 5)
        (= Coin_G 6)
        (= Coin_H 7)
        (= Coin_I 8)

        ; Starting locations
        (= (Coin_Location_X Coin_A 0) 0)
        (= (Coin_Location_Y Coin_A 0) 0)

        (= (Coin_Location_X Coin_B 0) 1)
        (= (Coin_Location_Y Coin_B 0) 0)

        (= (Coin_Location_X Coin_C 0) 2)
        (= (Coin_Location_Y Coin_C 0) 0)

        (= (Coin_Location_X Coin_D 0) 3)
        (= (Coin_Location_Y Coin_D 0) 0)

        (= (Coin_Location_X Coin_E 0) 4)
        (= (Coin_Location_Y Coin_E 0) 0)

        (= (Coin_Location_X Coin_F 0) 5)
        (= (Coin_Location_Y Coin_F 0) 0)

        (= (Coin_Location_X Coin_G 0) 6)
        (= (Coin_Location_Y Coin_G 0) 0)

        (= (Coin_Location_X Coin_H 0) 7)
        (= (Coin_Location_Y Coin_H 0) 0)

        (= (Coin_Location_X Coin_I 0) 8)
        (= (Coin_Location_Y Coin_I 0) 0)
    )
)



(assert 
(and
    Coin_Constrains

    (forall ((T Int) (C Int))
        (implies
            (<= 0 C 8)
            (and
                ; X is simply bounded between 0 and 12
                (<= 0 (Coin_Location_X C T) 12)
                ; Y can only be 1, if X is either 3, 5 or 7
                (ite
                    (or
                        (= (Coin_Location_X C T) 3)
                        (= (Coin_Location_X C T) 5)
                        (= (Coin_Location_X C T) 7)
                    )
                    ; Y can be 0 or 1
                    (or
                        (= (Coin_Location_Y C T) 0)
                        (= (Coin_Location_Y C T) 1)
                    )
                    ; Y can only be 0
                    (= (Coin_Location_Y C T) 0)
                )
            )
        )
    )

    ; No 2 coins can ever have the same location
    (forall ((T Int) (C1 Int) (C2 Int))
        (implies
            (and
                (<= 0 C1 8)
                (<= 0 C2 8)
                (not (= C1 C2))
            )
            (not
                (and
                    (= (Coin_Location_X C1 T) (Coin_Location_X C2 T))
                    (= (Coin_Location_Y C1 T) (Coin_Location_Y C2 T))
                )
            )
        )
    )

    (exists ((T Int))
        
    )

    ; As time moves from 1 point to the next, a single coin moves to a free location
    ; (forall ((T1 Int) (T2 Int))
    ;     (implies
    ;         (and
    ;             (= (+ T1 1) T2)
    ;         )
    ;         ; exits?
    ;         (exists ((C Int))
    ;             (and
    ;                 (<= 0 C 8)
    ;                 (or
    ;                     ; Move right
    ;                     (= (Coin_Location_X C T2) (+ (Coin_Location_X C T2) 1))
    ;                     ; Move left
    ;                     (= (Coin_Location_X C T2) (- (Coin_Location_X C T2) 1))
    ;                     ; Move up
    ;                     (= (Coin_Location_Y C T2) (+ (Coin_Location_Y C T2) 1))
    ;                     ; Move down
    ;                     (= (Coin_Location_Y C T2) (- (Coin_Location_Y C T2) 1))
    ;                 )
    ;             )
    ;         )
    ;     )
    ; )

); End of and
); End of assert


(check-sat)
(get-model)
; (get-value (
;     (Coin_Location_X Coin_A 0)
;     (Coin_Location_Y Coin_A 0)

;     (Coin_Location_X Coin_B 0)
;     (Coin_Location_Y Coin_B 0)

;     (Coin_Location_X Coin_C 0)
;     (Coin_Location_Y Coin_C 0)

;     (Coin_Location_X Coin_D 0)
;     (Coin_Location_Y Coin_D 0)

;     (Coin_Location_X Coin_E 0)
;     (Coin_Location_Y Coin_E 0)

;     (Coin_Location_X Coin_F 0)
;     (Coin_Location_Y Coin_F 0)

;     (Coin_Location_X Coin_G 0)
;     (Coin_Location_Y Coin_G 0)

;     (Coin_Location_X Coin_H 0)
;     (Coin_Location_Y Coin_H 0)

;     (Coin_Location_X Coin_I 0)
;     (Coin_Location_Y Coin_I 0)
; ))