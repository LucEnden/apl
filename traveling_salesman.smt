; Traveling Salesman (***)
; Make use of Z3 to find the cheapest path to visit all six ‘cities’ in this picture. 
; (The numbers along the edges indicate the travelcost between the cities).

; Vertexes
(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)
(declare-const E Int)
(declare-const F Int)
(define-fun VertexConstrains () Bool
    ; Vertices need to be unique 
    ; I dont use distinct, which would be more suiteable for a generalized solution
    ; But I will only be focusing on the graph from the excersises PDF.
    (and
        (= A 1)
        (= B 2)
        (= C 3)
        (= D 4)
        (= E 5)
        (= F 6)
    )
)

; An edge is defined as a function on 2 vertexes, which returns a number representing the travelcost from vertex A to B
(declare-fun Edge (Int Int) Int)
(declare-fun ValidEdge (Int Int) Bool)
(define-fun EdgeContstrains () Bool
    (and
        ; Edge weights
        (= (Edge A B) 6)
        (= (Edge A C) 7)
        (= (Edge B C) 1)
        (= (Edge B D) 4)
        (= (Edge B E) 3)
        (= (Edge C E) 2)
        (= (Edge C F) 1)
        (= (Edge D E) 5)
        (= (Edge E F) 3)

        ; Valid edges
        (forall ((m Int)(n Int))
            (implies
                ; The vertexes being between 1 and 6 and not equal ...
                (and
                    (<= 1 m 6)
                    (<= 1 n 6)
                    (not (= m n))
                    (> (Edge m n) 0)
                )
                ; Edges are valid if there weight is greater then 0
                (
                    
                )
            )
        )
        ; (implies
        ;     ()
        ;     ()
        ; )
        ; (= (ValidEdge A B) true)
        ; (= (ValidEdge A C) true)
        ; (= (ValidEdge B C) true)
        ; (= (ValidEdge B D) true)
        ; (= (ValidEdge B E) true)
        ; (= (ValidEdge C E) true)
        ; (= (ValidEdge C F) true)
        ; (= (ValidEdge D E) true)
        ; (= (ValidEdge E F) true)
    )
)

; A salesman's path is defined as a function on all vertexes (A trough F, in any order), that returns the travel cost 
; This allows simple ranking of paths by there total travel cost sum
(define-fun SalesPath ((V1 Int) (V2 Int)) Int
    ; ...
)

(assert 
(and

; ...

) ; end of and
) ; end of assert

(check-sat)
(get-model)