; Page 10 of modeling exercises:

; We want to test 6 medicines, but the tests are very expensive. In order to save costs, and 
; yet to make sure that enough combinations of medicines will be tested, we want to set up a 
; cost-effective scheme, testing the medicines in a number of rounds. 
; Let Z3 find out whether or not a schema can be found to test the medicines according to the 
; following conditions, and if it can be done, present Z3's answer in a nice, human-readable 
; format.

; There  are 10 test rounds 
; - In each round, 3 (different) medicines are tested 
; - Every medicine is tested 5 times (i.e. in 5 different rounds 
; - Every pair of (two) medicines occurs together in 2 and no more than 2 rounds 

; (This is called a (6,3,2)-design, see https://en.wikipedia.org/wiki/Block_design)

; see "medicine_testing_A.md" for a more intuitive explanation
(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)
(declare-const E Int)
(declare-const F Int)

(assert

; Each medicine is a number between 0 and 1 inclusivly
(and
(<= 1 A)
(<= 1 B)
(<= 1 C)
(<= 1 D)
(<= 1 E)
(<= 1 F)
(= (+ A B C D E F) 3)
)
; 1 round = 3 medicine
; i.e. adding up all the medicine values should equal 3
; (= (+ A B C D E F) 3)

)

(check-sat)
(get-model)