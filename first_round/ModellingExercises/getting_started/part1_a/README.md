## Question  
>	Find boolean values for A,B,C,D and E such that the following formula becomes true
>   (¬A ⇒ (B ∧ D)) ∧ (¬B ∨ ¬C ∨ E) ∧ ¬ (¬C ⇔ (¬A ∧ B)) ∧ ¬E ∧ D

## Notes
I used the list of logic symbols from wikipedia as a cheat sheet, as I am completely new to notation style of logic.
https://en.wikipedia.org/wiki/List_of_logic_symbols
> ¬ reads as "not"  
> ⇒ reads as "implies, if P then Q, it is not the case that P and not Q"  
> ∧ reads as "and"  
> ∨ reads as "or"  

Using the cheat sheet I translated the formula to the following formula in prefix/smt notation.
> (and (implies (not A) (and B D)) (and (or (not B) (or (not C) E)) (not (and (implies (not C) (and (not A) B)) (and (not E) D)))))

## Attempt 1

*Implementation:*
```smt
(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)
(declare-const E Bool)

(assert (and (implies (not A) (and B D)) (and (or (not B) (or (not C) E)) (not (and (implies (not C) (and (not A) B)) (and (not E) D))))))

(check-sat)
(get-model)
```

*Output:*
```bash
$ z3 ./solution.smt
sat
(
  (define-fun A () Bool
    true)
  (define-fun D () Bool
    true)
  (define-fun B () Bool
    true)
  (define-fun C () Bool
    false)
  (define-fun E () Bool
    false)
)
```

*Reflection:*  
I do not understand the formula well enough to explain why the output is correct. What I did do was to use the truth table tool to verify the output.
https://web.stanford.edu/class/cs103/tools/truth-table-tool/

This does kind of feel a lot like cheating, as I am using just another tool to verify another tools outcome. I used this tool mostly to save myself some time tho, as I feel like I am familiar enough with truth tables to be able to do this by hand given enough time. Regardless, I will ask for feedback on the proposed solution before continuing to the next exercise.