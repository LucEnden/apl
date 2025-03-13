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
    ; I dont use distinct, which would be more suiteable for a generalized solution ...
    ; But I will only be focusing on the graph from the excersises PDF, so hard coding them seems fine for now.
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
(define-fun EdgeCostContstrains () Bool
    (and
        ; Edge costs default to 0
        ; ...

        ; Provided costs function values
        (= (Edge A B) 6)
        (= (Edge A C) 7)
        (= (Edge B C) 1)
        (= (Edge B D) 4)
        (= (Edge B E) 3)
        (= (Edge C E) 2)
        (= (Edge C F) 1)
        (= (Edge D E) 5)
        (= (Edge E F) 3)

        ; Edge's travel costs are the same, regardless of direction 
        (forall ((v1 Int) (v2 Int) (c Int))
            (implies
                (= (Edge v1 v2) c)
                (= (Edge v2 v1) c)
            )
        )
    )
)

; An edge is valid if and only if the value for Edge which is given the same vertices as for ValidEdge is greater then 0 
(declare-fun ValidEdge (Int Int) Bool)
(define-fun ValidEdgeContstrains () Bool
    (and
        (forall ((v1 Int)(v2 Int))
            (implies
                (and ; Edges are valid if 
                    ; the cost is greater then 0
                    (> 0 (Edge v1 v2)) 
                    ; the provided vertexes are not the same
                    (not (= v1 v2))
                )
                (= (ValidEdge v1 v2) true)
            )
        )
    )
)

; A salesman's path is defined as a function on all vertexes (A trough F, in any order), that returns the travel cost 
; This allows simple ranking of paths by the sum of edges
; (define-fun SalesPath ((V1 Int) (V2 Int) (V3 Int) (V4 Int) (V5 Int) (V6 Int)) Int
;     ; ...
; )

(assert 
(and

VertexConstrains
EdgeCostContstrains
ValidEdgeContstrains

) ; end of and
) ; end of assert

(check-sat)
; (get-model)
(get-value (
    ; Does the inverse travel cost constain work?
    (Edge A B)
    (=
        (Edge A B)
        (Edge B A)
    ) ; Expected = True

    ; Show that the ValidEdge function is true for at least vertex A
    (ValidEdge A B) ; True
    (ValidEdge A C) ; True
    (ValidEdge A D) ; False
    (ValidEdge A E) ; False
    (ValidEdge A F) ; False
    (ValidEdge A 7) ; False
))