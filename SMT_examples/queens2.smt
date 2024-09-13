
; Position of queen nr i is (X i) (Y i)
(declare-fun X (Int) Int)
(declare-fun Y (Int) Int)

(assert (and

; Every queen has a position on the 8x8 board:
(forall ((i Int))
	(implies
		(<= 1 i 8)
		(and
			(<= 1 (X i) 8)
			(<= 1 (Y i) 8)
		)
	)
)

; No queen in the same row:
(distinct (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7) (X 8))

; No queen in the same column:
(distinct (Y 1) (Y 2) (Y 3) (Y 4) (Y 5) (Y 6) (Y 7) (Y 8))

; No two queens on the same 'upward' diagonal:
(distinct 
	(- (X 1) (Y 1)) 
	(- (X 2) (Y 2)) 
	(- (X 3) (Y 3)) 
	(- (X 4) (Y 4)) 
	(- (X 5) (Y 5)) 
	(- (X 6) (Y 6)) 
	(- (X 7) (Y 7)) 
	(- (X 8) (Y 8)) 
)

; No two queens on the same 'downward' diagonal:
(distinct 
	(+ (X 1) (Y 1)) 
	(+ (X 2) (Y 2)) 
	(+ (X 3) (Y 3)) 
	(+ (X 4) (Y 4)) 
	(+ (X 5) (Y 5)) 
	(+ (X 6) (Y 6)) 
	(+ (X 7) (Y 7)) 
	(+ (X 8) (Y 8)) 
)

))

(check-sat)
(get-value (
 (X 1) (Y 1)
 (X 2) (Y 2)
 (X 3) (Y 3)
 (X 4) (Y 4)
 (X 5) (Y 5)
 (X 6) (Y 6)
 (X 7) (Y 7)
 (X 8) (Y 8)
))