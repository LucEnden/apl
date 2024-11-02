; Page 10 of modeling exercises:
;   There  are 10 test rounds 
;   - In each round, 3 (different) medicines are tested 
;   - Every medicine is tested 5 times (i.e. in 5 different rounds)
;   - Every pair of (two) medicines occurs together in 2 and no more than 2 rounds 
;   (This is called a (6,3,2)-design, see https://en.wikipedia.org/wiki/Block_design)

; see "medicine_testing_A.md" for a my thought process and intuitive explanation's

(define-fun T (Int Int) Bool) ; Hinted to me by Timo, the use of an abstract function to model a test round (`T`). The arguments being the round number and 

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

; Every pair of (two) medicines occurs together in 2 and no more than 2 rounds 
(forall ((m1 Int) (m2 Int))
    
)

(check-sat)
(get-model)