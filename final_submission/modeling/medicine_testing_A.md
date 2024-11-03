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

---
3/11/2024

I solved it, but again, not without the help of the example.

The forall I copied (`In each round, (exactly) 3 medicines are tested`) was an inspiration for how I could implement the `Every medicine is tested 5 times` constrained on the domain.
I tried to do the same for the `Every pair of (two) medicines occurs together in 2 and no more than 2 rounds` constrained, but I just could not quite figure out how to do so, until I saw the implies in the exampele.