; Let i = point in time,

; Puzzle square identifiers are as bellow:
; |   |   |   | 5 |   | 8 |   | 11 |    |    | 
; | 1 | 2 | 3 | 4 | 6 | 7 | 9 | 10 | 12 | 13 |

; Coordinates start at 1,
; This makes square 1 X = 1 and Y = 1, square 5 X = 4 and Y = 2, etc.

; Location for square s is (X s) (Y s)
(declare-fun SquareX (Int) Int)
(declare-fun SquareY (Int) Int)

; Location at i for coin c is (X c i) (Y c i)
(declare-fun CoinX (Int Int) Int)
(declare-fun CoinY (Int Int) Int)

; Function to move coin c at i to square s is (MoveCoin c i s)
; Returns true if the coin can move to that square, false otherwise
(declare-fun MoveCoin (Int Int Int) Bool)

(assert (and

; Define the coordinates of the squares (wich are static and known)
(and
    ; First square (where the red coin orriginaly resides in)
    (= (SquareX 1) 1)
    (= (SquareY 1) 1)
    ; Second square, etc...
    (= (SquareX 2) 2)
    (= (SquareY 2) 1)
    
    (= (SquareX 3) 3)
    (= (SquareY 3) 1)
    ; First square with a neighbor on top
    (= (SquareX 4) 4)
    (= (SquareY 4) 1)
    (= (SquareX 5) 4)
    (= (SquareY 5) 2)

    (= (SquareX 6) 5)
    (= (SquareY 6) 1)

    ; Second square with a neighbor on top
    (= (SquareX 7) 6)
    (= (SquareY 7) 1)
    (= (SquareX 8) 6)
    (= (SquareY 8) 2)
    
    (= (SquareX 9) 7)
    (= (SquareY 9) 1)
    
    (= (SquareX 10) 8)
    (= (SquareY 10) 1)
    (= (SquareX 11) 8)
    (= (SquareY 11) 2)
    
    (= (SquareX 12) 9)
    (= (SquareY 12) 1)

    (= (SquareX 13) 10)
    (= (SquareY 13) 1)
)

; Define starting coordinates of the coins (which are only known for i = 1)
(and
    (= (CoinX 1 1) 1)
    (= (CoinY 1 1) 1)
    
    (= (CoinX 2 1) 2)
    (= (CoinY 2 1) 1)
    
    (= (CoinX 3 1) 3)
    (= (CoinY 3 1) 1)
    
    (= (CoinX 4 1) 4)
    (= (CoinY 4 1) 1)
    
    (= (CoinX 5 1) 5)
    (= (CoinY 5 1) 1)
    
    (= (CoinX 6 1) 6)
    (= (CoinY 6 1) 1)
    
    (= (CoinX 7 1) 7)
    (= (CoinY 7 1) 1)
    
    (= (CoinX 8 1) 8)
    (= (CoinY 8 1) 1)
    
    (= (CoinX 9 1) 9)
    (= (CoinY 9 1) 1)
)

; MoveCoin is true only when the square the coin wants to move to is free
(forall ((i Int) (c Int) (s Int))
    (implies
        (and
            (<= 1 c 9)  ; 9 coins
            (<= 1 s 13) ; 13 squares
        )
        (and
            
        )
    )
)

; TODO: introduce huristic that no coin can move back to the square it just came from, unles N rounds have passed

)) ; End of assert

(check-sat)
(get-model)