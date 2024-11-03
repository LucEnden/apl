; Page 10 of modeling exercises:
;   There  are 10 test rounds 
;   - In each round, 3 (different) medicines are tested 
;   - Every medicine is tested 5 times (i.e. in 5 different rounds)
;   - Every pair of (two) medicines occurs together in 2 and no more than 2 rounds 
;   (This is called a (6,3,2)-design, see https://en.wikipedia.org/wiki/Block_design)
; See "./medicine_testing_A.md" for a my thought process and intuitive explanation's

(declare-fun T (Int Int) Bool) ; Hinted to me by Timo Rasenberg, the use of an abstract function to model a test round (`T`). 
; The arguments being the round number and the medicine (respecitvly)
; Return true or false depending on whether the given medicine is being tested in the given round or not.

(assert (and

; In each round, 3 (different) medicines are tested 
(forall ((r Int))
	(= 3
		(+ 
			(ite (T r 1) 1 0)
			(ite (T r 2) 1 0)
			(ite (T r 3) 1 0)
			(ite (T r 4) 1 0)
			(ite (T r 5) 1 0)
			(ite (T r 6) 1 0)
		)
	)
)

; Every medicine is tested 5 times (i.e. in 5 different rounds)
(forall ((m Int))
    (= 5
        (+
            (ite (T 1  m) 1 0)
            (ite (T 2  m) 1 0)
            (ite (T 3  m) 1 0)
            (ite (T 4  m) 1 0)
            (ite (T 5  m) 1 0)
            (ite (T 6  m) 1 0)
            (ite (T 7  m) 1 0)
            (ite (T 8  m) 1 0)
            (ite (T 9  m) 1 0)
            (ite (T 10 m) 1 0)
        )
    )
)

; Every pair of (two) medicines occurs together in 2 and no more than 2 rounds 
(forall ((m1 Int) (m2 Int))
    (implies ; in the excersize it is implied that ...
        (and
            ; there are only 6 medicine (i.e. 1 trough 6 inclusive), and ...
            (<= 1 m1 6)
            (<= 1 m2 6)
            ; the medicine are unique (any given medicine tested can not be repeated in the same round)
            (distinct m1 m2)
        )
        (= 2
            (+
                (ite (and (T 1  m1) (T 1  m2)) 1 0)
                (ite (and (T 2  m1) (T 2  m2)) 1 0)
                (ite (and (T 3  m1) (T 3  m2)) 1 0)
                (ite (and (T 4  m1) (T 4  m2)) 1 0)
                (ite (and (T 5  m1) (T 5  m2)) 1 0)
                (ite (and (T 6  m1) (T 6  m2)) 1 0)
                (ite (and (T 7  m1) (T 7  m2)) 1 0)
                (ite (and (T 8  m1) (T 8  m2)) 1 0)
                (ite (and (T 9  m1) (T 9  m2)) 1 0)
                (ite (and (T 10 m1) (T 10 m2)) 1 0)
            )
        )
    )
)

)) ; End of assert

(check-sat)
(get-value (
	(T 1 1)
	(T 1 2)
	(T 1 3)
	(T 1 4)
	(T 1 5)
	(T 1 6)

	(T 2 1)
	(T 2 2)
	(T 2 3)
	(T 2 4)
	(T 2 5)
	(T 2 6)

	(T 3 1)
	(T 3 2)
	(T 3 3)
	(T 3 4)
	(T 3 5)
	(T 3 6)

	(T 4 1)
	(T 4 2)
	(T 4 3)
	(T 4 4)
	(T 4 5)
	(T 4 6)

	(T 5 1)
	(T 5 2)
	(T 5 3)
	(T 5 4)
	(T 5 5)
	(T 5 6)

	(T 6 1)
	(T 6 2)
	(T 6 3)
	(T 6 4)
	(T 6 5)
	(T 6 6)

	(T 7 1)
	(T 7 2)
	(T 7 3)
	(T 7 4)
	(T 7 5)
	(T 7 6)

	(T 8 1)
	(T 8 2)
	(T 8 3)
	(T 8 4)
	(T 8 5)
	(T 8 6)

	(T 9 1)
	(T 9 2)
	(T 9 3)
	(T 9 4)
	(T 9 5)
	(T 9 6)

	(T 10 1)
	(T 10 2)
	(T 10 3)
	(T 10 4)
	(T 10 5)
	(T 10 6)
))