(push 1)

(declare-const A Bool)
(declare-const B Bool)

(assert(distinct
	(xor A B)
	(= 
		(+
			(ite A 1 0)
			(ite B 1 0)
		)
		1
	)
))

(check-sat) ; output=unsat: for 2 variables, xor is the same as the +/ite construct (there's no model that makes the two come out as different)
;(get-model)

(pop 1)
(push 1)

(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)

(assert (distinct
	(xor A B C)
	(= 
		(+
			(ite A 1 0)
			(ite B 1 0)
			(ite C 1 0)
		)
		1
	)
))

(check-sat); sat: for 3 variables, xor is not the same as the +/ite construct
(get-model)   ;  (xor true true true) evaluates to true, rather than to false

(pop 1)
