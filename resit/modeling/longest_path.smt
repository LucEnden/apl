; Longest Path (**) 
; Eight points are positioned in a circle. We'll walk along the points, walking from one point to 
; another, in such a way that: 
; - we never walk across the same pair-of-points more than once, in either direction 
; - we never walk from a point to one of its two direct neighbouring points 

; Let Z3 find a walking path that satisfies the above constraints and is of maximal length 
; (where length means the number of steps, not physical length). 

(declare-const P1 Int)