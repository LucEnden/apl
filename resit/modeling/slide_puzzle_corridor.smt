; Slide puzzle (corridor) (****)
; Slide coins to empty positions. The red coin should end up at the empty spot at the right end.
; Model this with SMT and let Z3 find a solution.


; Square identifiers are as bellow:
; |   |   |   | E |   | H |   | K |   |   | 
; | A | B | C | D | F | G | I | J | L | M |
(declare-const SquareA Int)
(declare-const SquareB Int)
(declare-const SquareC Int)
(declare-const SquareD Int)
(declare-const SquareE Int)
(declare-const SquareF Int)
(declare-const SquareG Int)
(declare-const SquareH Int)
(declare-const SquareI Int)
(declare-const SquareJ Int)
(declare-const SquareK Int)
(declare-const SquareL Int)
(declare-const SquareM Int)


; Coin identifiers are as bellow (these are there starting possitions):
; |   |   |   |   |   |   |   |   |   |   | 
; | A | B | C | D | E | F | G | H | I |   |
(declare-const CoinA Int)
(declare-const CoinB Int)
(declare-const CoinC Int)
(declare-const CoinD Int)
(declare-const CoinE Int)
(declare-const CoinF Int)
(declare-const CoinG Int)
(declare-const CoinH Int)
(declare-const CoinI Int)


; Coin's have a location (X / Y) at point in time T
(declare-fun Coin_X (Int Int) Int)
(declare-fun Coin_Y (Int Int) Int)


; Coins there X and Y need to be in bounds of the puzzle at all times
; No coin can have its X/Y be equal to any other coin accross all points in time
; 