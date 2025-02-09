(set-logic QF_UF)
(declare-sort U 0)
(declare-sort I 0)
(declare-fun unit () I)
(declare-fun op (I I) I)
(declare-fun e5 () I)
(declare-fun e4 () I)
(declare-fun e3 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)
(assert (and (and (and (or (not (= (op e0 (op e0 e0)) e0)) (= e0 unit)) (or (not (= (op e1 (op e1 e1)) e1)) (= e1 unit))) (or (not (= (op e2 (op e2 e2)) e2)) (= e2 unit))) (or (not (= (op e3 (op e3 e3)) e3)) (= e3 unit))))
(assert (not (or (not (= (op e3 (op e3 e3)) e3)) (= e3 unit))))
(check-sat)
(exit)
