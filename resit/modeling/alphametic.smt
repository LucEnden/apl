(declare-const A Int)
(declare-const E Int)
(declare-const F Int)
(declare-const H Int)
(declare-const I Int)
(declare-const N Int)
(declare-const R Int)
(declare-const T Int)
(declare-const U Int)
(declare-const W Int)

(assert
(and
	; Numbers will be handeled in base 10
    (<= 0 A 9)
    (<= 0 E 9)
    (<= 0 F 9)
    (<= 0 H 9)
    (<= 0 I 9)
    (<= 0 N 9)
    (<= 0 R 9)
    (<= 0 T 9)
    (<= 0 U 9)
    (<= 0 W 9)

	; Numbers must be unique
	(distinct A E F H I N R T U W)
	; (distinct A B C D E F G H I J K L M N O P Q R S T U V W X Y Z) ; This is extremly slow, why?

	; First letter can not be 0
	(not (= E 0))
	(not (= A 0))
	(not (= F 0))
	(not (= W 0))
	(not (= N 0))

	; Sum of parts needs to be equal to the result
	(=
        (+ ; add all parts together
            (+
                (* E 10000)
                (* A 1000)
                (* R 100)
                (* T 10)
                (* H 1)
            )
            (+
                (* A 100)
                (* I 10)
                (* R 1)
            )
            (+
                (* F 1000)
                (* I 100)
                (* R 10)
                (* E 1)
            )
            (+
                (* W 10000)
                (* A 1000)
                (* T 100)
                (* E 10)
                (* R 1)
            )
        )
        ; compare to result
        (+
            (* N 100000)
            (* A 10000)
            (* T 1000)
            (* U 100)
            (* R 10)
            (* E 1)
        )
	)
)) ; end of assert

(check-sat)
(get-model)