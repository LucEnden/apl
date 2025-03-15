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
    (and
        (= A 1)
        (= B 2)
        (= C 3)
        (= D 4)
        (= E 5)
        (= F 6)
    )
)
(define-fun ValidVertex ((v Int)) Bool
    (<= 1 v 6)
)


; An edge is defined as a function on 2 vertexes, which returns a number representing the travelcost from vertex A to B
(declare-fun Edge (Int Int) Int)
(define-fun EdgeCostContstrains () Bool
    (and
        ; Define provided edge costs
        (= (Edge A B) 6)
        (= (Edge A C) 7)
        (= (Edge B C) 1)
        (= (Edge B D) 4)
        (= (Edge B E) 3)
        (= (Edge C E) 2)
        (= (Edge C F) 1)
        (= (Edge D E) 5)
        (= (Edge E F) 3)

        ; Edge costs is always 0, unless explicitly specified above
        (forall ((v1 Int) (v2 Int))
            (implies
                (not
                    (or
                        (and (= v1 A) (= v2 B)) 
                        (and (= v1 B) (= v2 A))

                        (and (= v1 A) (= v2 C))
                        (and (= v1 C) (= v2 A))

                        (and (= v1 B) (= v2 C))
                        (and (= v1 C) (= v2 B))

                        (and (= v1 B) (= v2 D))
                        (and (= v1 D) (= v2 B))

                        (and (= v1 B) (= v2 E))
                        (and (= v1 E) (= v2 B))

                        (and (= v1 C) (= v2 E))
                        (and (= v1 E) (= v2 C))

                        (and (= v1 C) (= v2 F))
                        (and (= v1 F) (= v2 C))

                        (and (= v1 D) (= v2 E))
                        (and (= v1 E) (= v2 D))

                        (and (= v1 E) (= v2 F))
                        (and (= v1 F) (= v2 E))
                    )
                )
                ; Default to 0
                (= (Edge v1 v2) 0)
            )
        )

        ; Edge's travel costs are the same, regardless of direction 
        (forall ((v1 Int) (v2 Int) (c Int))
            (implies
                (= (Edge v1 v2) c)
                (= (Edge v2 v1) c)
            )
        )
    )
)


; Edge's are modeled to be valid if and only if the value for Edge which is given the same vertices as for ValidEdge is greater then 0 
(define-fun ValidEdge ((v1 Int) (v2 Int)) Bool
    (> (Edge v1 v2) 0)
)


(define-fun ValidPath ((v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int)) Bool
    (and
        (distinct v1 v2 v3 v4 v5 v6)
        (ValidVertex v1)
        (ValidVertex v2)
        (ValidVertex v3)
        (ValidVertex v4)
        (ValidVertex v5)
        (ValidVertex v6)
        (ValidEdge v1 v2)
        (ValidEdge v2 v3)
        (ValidEdge v3 v4)
        (ValidEdge v4 v5)
        (ValidEdge v5 v6)
    )
)


; A salesman's path is defined as a function on all provided vertexes that returns the travel cost 
; This allows simple ranking of paths by the sum of edges
(define-fun SalesPath ((v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int)) Int
    (ite
        (ValidPath v1 v2 v3 v4 v5 v6)
        (+
            (Edge v1 v2)
            (Edge v2 v3)
            (Edge v3 v4)
            (Edge v4 v5)
            (Edge v5 v6)
        )
        0 
    )
)


; Variables used to construct the shortest path
(declare-const P1 Int)
(declare-const P2 Int)
(declare-const P3 Int)
(declare-const P4 Int)
(declare-const P5 Int)
(declare-const P6 Int)
(declare-const ShortestPath Int)


(assert
(and

    VertexConstrains
    EdgeCostContstrains
    (ValidPath P1 P2 P3 P4 P5 P6)
    (= ShortestPath (SalesPath P1 P2 P3 P4 P5 P6))

) ; end of AND
) ; end of ASSERT
(minimize ShortestPath)


(check-sat)
(get-value (
    P1 P2 P3 P4 P5 P6
    (SalesPath P1 P2 P3 P4 P5 P6)
    ShortestPath
))


; Sanity checks, left here for archiving purposes
; (get-value (
;     (Edge -1 -1)                ; Expected: 0
;     (Edge 0 0)                  ; Expected: 0
;     (Edge 1 1)                  ; Expected: 0
;     (Edge 1 2)                  ; Expected: 6
;     (Edge A B)                  ; Expected: 6
;     (= (Edge 1 2) (Edge A B) )  ; Expected: true
;     (= (Edge A B) (Edge B A) )  ; Expected: true
    
;     (SalesPath A B C D E F)     ; Expected: 0 (no edge from C to D)
;     (SalesPath A B C F E D)     ; Expected: 6 + 1 + 1 + 3 + 5 = 16
;     ; Sales path above was calculated by hand to be one of two shortests for the specified graph:
;     ; Path: A -> B -> C -> F -> E -> D | Length: 16
;     ; Path: D -> E -> F -> C -> B -> A | Length: 16
; ))