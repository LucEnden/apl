## Knight’s Tour (***) 
Let Z3 find a path for the knight to visit every field on the chess board without ever visiting the same field twice. (If Z3 is too slow to find a path that covers all 64 fields, a shorter path will also do, as long as your solution could ‘in principle’ find the complete ‘tour’.)

## Model

- We hebben 1 paard
- We hebben 1 schaakboord van 8 * 8 = 64 vakken

- A valid move is one that
    - Updates the X by 2 and Y by 1, or ...
    - Updates the X by 1 and Y by 2, and ...
    - Updates the X within the bounds of the board
    - Updates the Y within the bounds of the board
