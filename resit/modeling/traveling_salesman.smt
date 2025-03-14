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

; A salesman's path is defined as a function on all provided vertexes (in order), that returns the travel cost 
; This allows simple ranking of paths by the sum of edges
; If any of the provided vertexes dont have a valid path 
(define-fun SalesPath ((v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int)) Int
    (ite
        ; Check whether the path is even valid before calculating its cost
        (and
            (ValidEdge v1 v2)
            (ValidEdge v2 v3)
            (ValidEdge v3 v4)
            (ValidEdge v4 v5)
            (ValidEdge v5 v6)
        )
        ; Return cost of path once its deemed valid
        (+
            (Edge v1 v2)
            (Edge v2 v3)
            (Edge v3 v4)
            (Edge v4 v5)
            (Edge v5 v6)
        )
        ; Return inavlid cost
        0 
    )
)

(assert 
(and

VertexConstrains
EdgeCostContstrains

) ; end of and
) ; end of assert

(check-sat)
; (get-model)
(get-value (
    (Edge -1 -1)                ; Expected: 0
    (Edge 0 0)                  ; Expected: 0
    (Edge 1 1)                  ; Expected: 0
    (Edge 1 2)                  ; Expected: 6
    (Edge A B)                  ; Expected: 6
    (= (Edge 1 2) (Edge A B) )  ; Expected: true

    ; Does the inverse travel cost constain work?
    (= (Edge A B) (Edge B A) ) ; Expected = true
))