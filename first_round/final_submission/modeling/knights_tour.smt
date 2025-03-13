; Knight’s Tour (***) 
; Let Z3 find a path for the knight to visit every field on the chess board 
; without ever visiting the same field twice. 

; Position of knight at step i is (X i) (Y i)
(declare-fun X (Int) Int)
(declare-fun Y (Int) Int)

(declare-const PATH_SIZE Int)
(declare-const BOARD_WIDTH Int)
(declare-const BOARD_HEIGHT Int)

; The knight has a particular L shape movement pattern it needs to abide by 
(define-fun LShape () Bool
    ; Restrict the knights movement
    (forall ((i Int))
        (implies
            (<= 1 i PATH_SIZE)
            (or
                (and ; right right up
                    (= (X (+ i 1)) (+ (X i) 2))
                    (= (Y (+ i 1)) (+ (Y i) 1))
                )
                (and ; right right down
                    (= (X (+ i 1)) (+ (X i) 2))
                    (= (Y (+ i 1)) (- (Y i) 1))
                )
                (and ; left left up
                    (= (X (+ i 1)) (- (X i) 2))
                    (= (Y (+ i 1)) (+ (Y i) 1))
                )
                (and ; left left down
                    (= (X (+ i 1)) (- (X i) 2))
                    (= (Y (+ i 1)) (- (Y i) 1))
                )
                (and ; right up up
                    (= (X (+ i 1)) (+ (X i) 1))
                    (= (Y (+ i 1)) (+ (Y i) 2))
                )
                (and ; right down down
                    (= (X (+ i 1)) (+ (X i) 1))
                    (= (Y (+ i 1)) (- (Y i) 2))
                )
                (and ; left up up
                    (= (X (+ i 1)) (- (X i) 1))
                    (= (Y (+ i 1)) (+ (Y i) 2))
                )
                (and ; left down down
                    (= (X (+ i 1)) (- (X i) 1))
                    (= (Y (+ i 1)) (- (Y i) 2))
                )
            )
        )
    )
)

; The knight can only move wihtin the confinds of the board
(define-fun BoardBounding () Bool
    ; For each step every step must fall on the board
    (forall ((i Int))
        (implies
            (<= 1 i PATH_SIZE)
            (and
                (<= 1 (X i) BOARD_WIDTH)
                (<= 1 (Y i) BOARD_HEIGHT)
            )
        )
    )
)

; All pairs of X/Y need to be unique for any given step
(define-fun NoRepeatedSteps () Bool
    (forall ((i Int) (j Int))
        (implies
            (and
                (<= 1 i PATH_SIZE)
                (<= 1 j PATH_SIZE)
                (distinct i j)
            )
            (not
                (and
                    (= 
                        (X i)
                        (X j)
                    )
                    (= 
                        (Y i)
                        (Y j)
                    )
                )
            )
        )
    )
)

(assert (and

(= PATH_SIZE 32)
(= BOARD_WIDTH 8)
(= BOARD_HEIGHT 8)

LShape
BoardBounding
NoRepeatedSteps

)) ; End of assert

(check-sat)
(get-value (
    (X 1)
    (Y 1)
    (X 2)
    (Y 2)
    (X 3)
    (Y 3)
    (X 4)
    (Y 4)
    (X 5)
    (Y 5)
    (X 6)
    (Y 6)
))