; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.

; This solution file was made with the reduced puzzle in mind (see `slide_puzzle_corridor_reduced.png`) as a proof of concept.
; Inspiration for datatypes and constrains where taken from `custom_type+quantifiers.smt` example.

(declare-datatypes () ((Coin Red A B C D)))
(declare-datatypes () ((Square Start One Two Three Four Five Six End)))


; Position of Coin at time T
(declare-fun Pos (Coin Int) Square)
(declare-const MaxT Int)
(declare-fun Adjacenct (Square Square) Bool)


(define-fun SquareIsFree ((S Square) (T Int)) Bool
    (not (exists ((C Coin))
        (= (Pos C T) S)
    ))
)


(define-fun BidirecitonalAdjecency () Bool
    (forall ((S1 Square) (S2 Square))
        (implies
            (Adjacenct S1 S2)
            (Adjacenct S2 S1)
        )
    )
)


(define-fun TryMoveTo ((C Coin) (Source Square) (Target Square) (T Int)) Bool
    (ite
        (and
            (SquareIsFree Target T)
            (Adjacenct Source Target)
            (not (= Source Target))
            (= (Pos C (- T 1)) Source)
        )
        (= (Pos C T) Target)
        (= (Pos C T) Source)
    )
)


(define-fun Puzzle1 () Bool
    (and
        ; Predefined adjecency
        (= (Adjacenct Start One) true)
        (= (Adjacenct One Two) true)
        (= (Adjacenct Two Three) true)
        (= (Adjacenct Two Five) true)
        (= (Adjacenct Three Four) true)
        (= (Adjacenct Four End) true)
        (= (Adjacenct Four Six) true)

        ; Adjecency is always false, unless explicitly specified above
        (forall ((S1 Square) (S2 Square))
            (implies
                (not
                    (or
                        (and (= S1 Start) (= S2 One))
                        (and (= S1 One) (= S2 Start))

                        (and (= S1 One) (= S2 Two))
                        (and (= S1 Two) (= S2 One))

                        (and (= S1 Two) (= S2 Three))
                        (and (= S1 Three) (= S2 Two))

                        (and (= S1 Two) (= S2 Five))
                        (and (= S1 Five) (= S2 Two))

                        (and (= S1 Three) (= S2 Four))
                        (and (= S1 Four) (= S2 Three))

                        (and (= S1 Four) (= S2 End))
                        (and (= S1 End) (= S2 Four))

                        (and (= S1 Four) (= S2 Six))
                        (and (= S1 Six) (= S2 Four))
                    )
                )
                ; Default to false
                (= (Adjacenct S1 S2) false)
            )
        )

        BidirecitonalAdjecency
        
        ; Starting positions
        (= (Pos Red 0) Start)
        ; (= (Pos A 0) One)
        ; (= (Pos B 0) Two)
        ; (= (Pos C 0) Three)
        ; (= (Pos D 0) Four)
    )
)


(assert
(and
    (= MaxT 2)
    Puzzle1

    (forall ((T Int) (C Coin))
        (forall ((Source Square) (Target Square))
            (TryMoveTo C Source Target T )
        )
    )

    ; (ite
    ;     (and
    ;         (SquareIsFree Target T)
    ;         (Adjacenct Source Target)
    ;         (not (= Source Target))
    ;         (= (Pos C (- T 1)) Source)
    ;     )
    ;     (= (Pos C T) Target)
    ;     (= (Pos C T) Source)
    ; )
    
); End of AND
); End of ASSERT

(check-sat)
; (get-model)
(get-value (
    (Pos Red 0)
	(Pos Red 1)
	(Pos Red 2)
	(Pos Red 3)
	(Pos Red 4)
	(Pos Red 5)
	(Pos Red 6)
	(Pos Red 7)
	(Pos Red 8)
	(Pos Red 9)
	(Pos Red 10)
	(Pos Red 11)
	(Pos Red 12)
	(Pos Red 13)
	(Pos Red 14)
	(Pos Red 15)
	(Pos Red 16)
	(Pos Red 17)
	(Pos Red 18)
	(Pos Red 19)
	(Pos Red 20)
	(Pos Red 21)
))