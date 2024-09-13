

(check-sat)
(get-value (
 (xor true false false)  ; true
 (xor false true false false) ; true
 (xor false true true false) ; false
 (xor true true true)  ; true (!!!???)

))
