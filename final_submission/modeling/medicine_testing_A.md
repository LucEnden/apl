## Assignemnt

Page 10 of modeling exercises:

> We want to test 6 medicines, but the tests are very expensive. In order to save costs, and 
> yet to make sure that enough combinations of medicines will be tested, we want to set up a 
> cost-effective scheme, testing the medicines in a number of rounds. 
> Let Z3 find out whether or not a schema can be found to test the medicines according to the 
> following conditions, and if it can be done, present Z3's answer in a nice, human-readable 
> format.

> There  are 10 test rounds 
> - In each round, 3 (different) medicines are tested 
> - Every medicine is tested 5 times (i.e. in 5 different rounds )
> - Every pair of (two) medicines occurs together in 2 and no more than 2 rounds 

> (This is called a (6,3,2)-design, see https://en.wikipedia.org/wiki/Block_design)

---

## Breakdown

Lets brake this problem down:
- "test 6 medicines", how can we represent 6 different medicines?
- "10 test rounds", we can represent the test rounds as an int T and limit it to be <= 10, but how can we represent a test round?
- "medicine ... tested ... in 5 different rounds", so each medicine can only be tested 5 times
- "pair of 2 medicine occers together ... no more then 2 rounds"
    - In other words, A and B cannot occur together in more then 2 test rounds
    - For example, if a test round is a list, then the first test round = [ A, B, C ] and the second round = [ A, B, D ], then their are no other test rounds in which A and B can occer together
    - This limits the amount of combinations we can test, thus we might not find an answer given certain implementations

## Domain and Limitations

### Medicine
The 6 medicines will be represented as integers
```smt
(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)
(declare-const E Int)
(declare-const F Int)
```

We limit each medicine to be either 1 (being tested) or 0 (not being tested).
```smt
(and
(<= 1 A)
(<= 1 B)
(<= 1 C)
(<= 1 D)
(<= 1 E)
(<= 1 F)
)
```

I dont know if we can write this in a neater way using a forall for example.
If I feel like it and I have time to spear i might test this out.
<!-- I tested this and it did not make sense to have a for all on multiple variables, as you would still have to enclose all of the values in an and case with each variable <= 5

(forall ((A)(B)(C)(D)(E)(F)))
    (and
        (<= 5 A)
        (<= 5 B)
        (<= 5 C)
        (<= 5 D)
        (<= 5 E)
        (<= 5 F)
    )
)

this also trew an error, so there is that!
-->



### Test Rounds
Test rounds will be represented as an integer.
```smt
(declare-const T Int)
```

We limit the amount of test rounds to 10
```smt
(<= T 10)
```

To emulate a test round I will be employing a custom fnuction
```smt
(declare-fun testRound ())
```

---
31/10/2024:

In full honesty: I just went trough the med.2.smt example for about 10 second to glance at how its done. What I saw that jumped out the most was:
- The SMT-LIB `(get-value ...)` for each of the individual medicine 
  (represented as unique integers from 1 trough 7, given the block design `7, 3, 2`). I found out already that my idea for representing the medicine as all values of 1 would not work, as their is no uniqueness in that setup to check whether any give one was tested, so it makes sence to see this
- the use of `ite` to sum up values 

---
1/11/2024

After one day of trying to find a solution on paper, and being unsuccesfull, I allowed myself to copy the first part of `med.2.smt`, which is the `(forall ((r Int)) ...`

The forall makes sense, it rougly translates to "for all rounds, the sum of the medicine"

