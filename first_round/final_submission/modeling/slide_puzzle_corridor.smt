(assert (and

(forall ((r Int))
    ; Does their exist a path the coins can take in order for the red coin to end up in the desired square
)

)) ; End of assert

(check-sat)
(get-model)