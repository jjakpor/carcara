(set-logic QF_UF)
(declare-sort U 0)
(declare-sort I 0)
(declare-fun op (I I) I)
(declare-fun e4 () I)
(declare-fun e3 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)
(assert (and (and (not (= (op e0 (op e0 e0)) e0)) (not (= (op e1 (op e1 e1)) e1))) (not (= (op e2 (op e2 e2)) e2))))
(assert (not (and (not (= (op e0 (op e0 e0)) e0)) (not (= (op e1 (op e1 e1)) e1)))))
(check-sat)
(exit)
