; Page 10 of modeling exercises:

; We want to test 7 medicines, and we are especially interested in the risks when using 
; combinations of them at the same time, but the tests are very expensive to perform. 
; Moreover, if too many medicines are tested at the same time, the results become 
; unreliable. 

; Hence, we want to design a schema of test rounds, satisfying the following constraints...
; - In each round, at most 3 (different) medicines are tested 
; - Every pair of (two) medicines occurs together in at least 2 rounds 
; - We want a scheme with as few tests done as possible

; Use Z3 to find out an optimal schema, and present Z3's answer in a nice, human-readable 
; format.