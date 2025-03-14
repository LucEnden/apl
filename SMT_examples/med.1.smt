; We have 7 medicines, to be tested in 7 test-rounds
; Subject to 2 constraints:
;  - Each round tests 3 medicine
;  - Every pair of medicines is tested together in one round and no more than one round

; The function T models whether or not a certain medicine is tested in a certain testround
; argument1: time/testround-number; argument2: medicine-number; 
; output: true if the indicated medicine is tested in the indicated round, false otherwise
; timepoints as well as medicines are numbered from 1 onwards
(declare-fun T (Int Int) Bool)

(assert (and

; In each round, (exactly) 3 medicines are tested
(forall ((r Int))
	(= 3
		(+ 
			(ite (T r 1) 1 0)
			(ite (T r 2) 1 0)
			(ite (T r 3) 1 0)
			(ite (T r 4) 1 0)
			(ite (T r 5) 1 0)
			(ite (T r 6) 1 0)
			(ite (T r 7) 1 0)
		)
	)
)

; (2nd condition, first part:) No pair of medicines occur together in more than one test round:
(not (exists ((m1 Int) (m2 Int) (r1 Int) (r2 Int))
	(and
		(<= 1 m1 7)
		(<= 1 m2 7)
		(<= 1 r1 7)
		(<= 1 r2 7)
		(distinct m1 m2)
		(distinct r1 r2)

		(T r1 m1)
		(T r1 m2)
		(T r2 m1)
		(T r2 m2)
	)
))

; (2nd condition, second part:) Every pair of medicines occurs together in at least one test round:

(forall ((m1 Int) (m2 Int))
	(implies
		(and
			(<= 1 m1 7)
			(<= 1 m2 7)
			(distinct m1 m2)
		)
		(exists ((r Int))
			(and
				(<= 1 r 7)
				(T r m1)
				(T r m2)
			)
		)
	)
)

))
(check-sat)
(get-value (
	(T 1 1)
	(T 1 2)
	(T 1 3)
	(T 1 4)
	(T 1 5)
	(T 1 6)
	(T 1 7)

	(T 2 1)
	(T 2 2)
	(T 2 3)
	(T 2 4)
	(T 2 5)
	(T 2 6)
	(T 2 7)

	(T 3 1)
	(T 3 2)
	(T 3 3)
	(T 3 4)
	(T 3 5)
	(T 3 6)
	(T 3 7)

	(T 4 1)
	(T 4 2)
	(T 4 3)
	(T 4 4)
	(T 4 5)
	(T 4 6)
	(T 4 7)

	(T 5 1)
	(T 5 2)
	(T 5 3)
	(T 5 4)
	(T 5 5)
	(T 5 6)
	(T 5 7)

	(T 6 1)
	(T 6 2)
	(T 6 3)
	(T 6 4)
	(T 6 5)
	(T 6 6)
	(T 6 7)

	(T 7 1)
	(T 7 2)
	(T 7 3)
	(T 7 4)
	(T 7 5)
	(T 7 6)
	(T 7 7)
))
