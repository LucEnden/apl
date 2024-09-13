## Question  
>	solve: x^2 + 115x + 3066  
>	Does it find both roots?

## Notes
It is insinuated that x crosses the 0 line 2 times, making this probably a parabol.
(I verified the above statement using desmos.com/calculator which was advised to me by Timo Rasenberg)

I want to start with translating the equation into a S-Expression
The equation is currently in infix, lets change that to prefix:
> \+ (+ (^ 2 x) (* 115 x)) 3066

## Attempt 1

*Implementation:*
```smt
(declare-const x Int)

(assert (= (+ (+ (* x x) (* 115 x)) 3066) 0))
;(assert (> (+ (+ (* x x) (* 115 x)) 3066) -42))

(check-sat)
(get-model)
```

*Output:*
```bash
$ z3 ./solution.smt
sat
(
  (define-fun x () Int
    (- 42))
)
```

*Reflection:*  
After some trial and error I found that the assert statement works for finding at least 1 value for x that satisfies the equation in the question. However as the question states I need to find both roots.  
I thought a hacky way of finding this would be to just take the output for x and do a second assert which checks for a value greater then the previously found one. This did not work unfortuntly, and it also indicates to me that I am still using my programmers mindset (comparing variables manually) instead of harnasing the power of z3 and let the tool do that for me.

## Attempt 2

```smt
(declare-const x1 Int)
(declare-const x2 Int)

;	In the assert bellow I check wheter their is a value for x such that the outcome of the equation from the question is 0 
(assert (= (+ (+ (* x1 x1) (* 115 x1)) 3066) 0))
;	In the assert bellow I check for the same exact equation (the equation from the question should probably be put into a function...), but now I also check wheter their is a value for x2 that is not equal to x2, in order to find the second root 
(assert (and (= (+ (+ (* x2 x2) (* 115 x2)) 3066) 0) (not (= x1 x2))))
;	in the assert above their is an assumption that x1 and x2 can not be equal integers

(check-sat)
(get-model)
```

*Output:*
```bash
$ z3 ./solution.smt
sat
(
  (define-fun x1 () Int
    (- 42))
  (define-fun x2 () Int
    (- 73))
)
```

EUREKA!  
The output for the 2 asserts in attempt 2 give me the expected answer.

*Reflections:*

By noticing my programmers mindset in the first attempt, paired with the assumtions made in that attempt (second root is greater then the previous one), i was able to correct for those mistakes in the second attempt, which in turn gave me the solution to the question.
I will be doing a final attempt, in which I plan on puting the equation inside a function (for DRY purposes) and using decimal representation for x1 and x2 instead of integers to verify take away the assumption that x1 and x2 can not be equal integers.

## Final Attempt

```smt
(declare-const x1 Real)
(declare-const x2 Real)

(define-fun my_fun ((x Real)) Real
    (+ (+ (* x x) (* 115 x)) 3066)
)

(assert (= (my_fun x1) 0))
(assert (and (= (my_fun x2) 0) (not (= x1 x2))))

(check-sat)
(get-model)
```

*Output:*
```bash
$ z3 ./solution.smt
sat
(
  (define-fun x1 () Real
    (- 42.0))
  (define-fun x2 () Real
    (- 73.0))
)
```

*Reflections:*
I am very happy with the final attempt, as it is the most clean and readable version of the 3 attempts, and that it also gives me the expected output.

Their are probably more "cleaner" ways to format the code, like for example changing the function to check the equation outcome for 0 inside of itself (changes `(assert (= (my_fun x1) 0))` to `(assert (my_fun x1))` and results in cleaner asserts), but this is something to take into account for future assigments.

It took me three days to get here, as i had to learn;
- how to use z3 and its syntax (which was harder then expected)
- what S-Expressions are and how to use them
- how to read prefix notation
- reflection on my mistakes and allowing time to have the knowledge sink in

I am happy with the result and the learning experience that came with the excersise.