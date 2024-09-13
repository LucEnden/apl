(declare-fun A (Int Int) Int)

; helper-function to more easily access entries in the 3x3 blocks
(define-fun B ((m Int)(n Int)(x Int)(y Int)) Int
	(A 
		(+ (* m 3) x)
		(+ (* n 3) y)
	)
)

(assert (and

; all entries are numbers from 1 to 9:
(forall ((m Int)(n Int))
	(implies
		(and
			(<= 1 m 9)
			(<= 1 n 9)
		)
		(<= 1 (A m n) 9)
	)
)

; rows, columns contain no duplicates:
(forall ((n Int))
	(implies
		(<= 1 n 9)
		(and
			(distinct (A 1 n) (A 2 n) (A 3 n) (A 4 n) (A 5 n) (A 6 n) (A 7 n) (A 8 n) (A 9 n)) 
			(distinct (A n 1) (A n 2) (A n 3) (A n 4) (A n 5) (A n 6) (A n 7) (A n 8) (A n 9))
		)
	)
)

; the 9 3x3 blocks contain no duplicates:
(forall ((m Int)(n Int))
	(implies
		(and
			(<= 1 m 3)
			(<= 1 n 3)
		)
		(distinct 
			(B m n 1 3) (B m n 2 3) (B m n 3 3)
			(B m n 1 2) (B m n 2 2) (B m n 3 2)
			(B m n 1 1) (B m n 2 1) (B m n 3 1)
		)
	)
)

; Specifying the puzzle:

(= (A 1 7) 8)
(= (A 2 1) 4)
(= (A 2 4) 2)
(= (A 2 5) 8)
(= (A 2 9) 6)
(= (A 3 6) 7)
(= (A 3 8) 3)
(= (A 4 3) 6)
(= (A 4 6) 3)
(= (A 4 8) 2)
(= (A 4 9) 1)
(= (A 5 1) 5)
(= (A 5 2) 4)
(= (A 5 5) 1)
(= (A 5 8) 7)
(= (A 5 9) 8)
(= (A 6 1) 1)
(= (A 6 2) 2)
(= (A 6 4) 5)
(= (A 6 7) 6)
(= (A 7 2) 7)
(= (A 7 4) 3)
(= (A 8 1) 3)
(= (A 8 5) 6)
(= (A 8 6) 1)
(= (A 8 9) 4)
(= (A 9 3) 5)

; .4. .51 .3.
; ... .42 7..
; ... 6.. ..5
; .2. ..5 3..  
; .8. .1. .6. 
; ..7 3.. .1.
; 8.. ..6 ...   
; ..3 27. ...    
; .6. 18. .4. 
	
))
(check-sat)
(get-value (

(A 1 1) (A 2 1) (A 3 1) (A 4 1) (A 5 1) (A 6 1) (A 7 1) (A 8 1) (A 9 1)
(A 1 2) (A 2 2) (A 3 2) (A 4 2) (A 5 2) (A 6 2) (A 7 2) (A 8 2) (A 9 2)
(A 1 3) (A 2 3) (A 3 3) (A 4 3) (A 5 3) (A 6 3) (A 7 3) (A 8 3) (A 9 3)
(A 1 4) (A 2 4) (A 3 4) (A 4 4) (A 5 4) (A 6 4) (A 7 4) (A 8 4) (A 9 4)
(A 1 5) (A 2 5) (A 3 5) (A 4 5) (A 5 5) (A 6 5) (A 7 5) (A 8 5) (A 9 5)
(A 1 6) (A 2 6) (A 3 6) (A 4 6) (A 5 6) (A 6 6) (A 7 6) (A 8 6) (A 9 6)
(A 1 7) (A 2 7) (A 3 7) (A 4 7) (A 5 7) (A 6 7) (A 7 7) (A 8 7) (A 9 7)
(A 1 8) (A 2 8) (A 3 8) (A 4 8) (A 5 8) (A 6 8) (A 7 8) (A 8 8) (A 9 8)
(A 1 9) (A 2 9) (A 3 9) (A 4 9) (A 5 9) (A 6 9) (A 7 9) (A 8 9) (A 9 9)

))