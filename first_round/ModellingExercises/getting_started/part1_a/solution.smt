(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)
(declare-const E Bool)

(assert (and (implies (not A) (and B D)) (and (or (not B) (or (not C) E)) (not (and (implies (not C) (and (not A) B)) (and (not E) D))))))

(check-sat)
(get-model)