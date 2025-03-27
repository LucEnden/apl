; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.

; This solution file was made with the reduced puzzle in mind (see `slide_puzzle_corridor_reduced.png`) as a proof of concept.
; Inspiration for datatypes and constrains where taken from `custom_type+quantifiers.smt` example.

(declare-datatypes () ((Coin Red BlueOne BlueTwo BlueThree)))
(declare-datatypes () ((Square Start One Two Three Four Five Six End)))
(declare-datatypes () ((Direction North East South West)))


; Position of Coin at time T
(declare-fun Pos (Coin Int) Square)
(declare-const MaxT Int)
(declare-fun Adjacenct (Square Square) Bool)


(define-fun PosIsEqual ((C1 Coin) (C2 Coin) (T Int)) Bool
    (= (Pos C1 T) (Pos C2 T))
)


(assert
(and
    (= MaxT 10)

    ; Starting positions
    (= (Pos Red 0) Start)
    (= (Pos BlueOne 0) One)
    (= (Pos BlueTwo 0) Two)
    (= (Pos BlueThree 0) Three)

    ; Define adjacency
    (and
        (= (Adjacenct Start One) true)
        (= (Adjacenct One Two) true)
        (= (Adjacenct Two Three) true)
        (= (Adjacenct Three Four) true)
        (= (Adjacenct Four End) true)
        (= (Adjacenct Two Five) true)
        (= (Adjacenct Four Six) true)

        ; Bidirecitonal adjecency
        (forall ((S1 Square) (S2 Square))
            (implies
                (Adjacenct S1 S2)
                (Adjacenct S2 S1)
            )
        )
    )

    ; NOTE: I dont need this, since PosIsEqual is fully defined. What I really need is to constrain the Pos function's change over time
    ; No 2 coins can ever have the same possition
    ; (forall ((C1 Coin) (C2 Coin) (T Int))
    ;     (implies
    ;         (and
    ;             (<= 0 T MaxT)
    ;             (not (= C1 C2))
    ;         )
    ;         (not (PosIsEqual C1 C2 T))
    ;     )
    ; )

    ; Possition change over time
    (forall ((C Coin) (T Int))
        (implies
            (<= 1 T MaxT) ; Start at 1 since possitions at T = 0 are predefined
            (and
                ; Move left
                ; Move right
                ; Move up
                ; Move down
                ; Dont move
                (= 
                    (Pos C T)
                    (Pos C (- T 1))
                )
            )
        )
    )
    
); End of AND
); End of ASSERT

(check-sat)
; (get-model)
(get-value (
    (Pos Red 0)
    (Pos Red 1)
    (Pos Red 2)
    (Pos Red 3)
))