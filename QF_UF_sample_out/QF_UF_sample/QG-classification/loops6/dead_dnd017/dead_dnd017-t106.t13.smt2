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
(assert (= e0 (op e2 (op e2 e0))))
(assert (= (op e2 (op e2 e0)) (op e2 e2)))
(assert (not (= e0 (op e2 e2))))
(check-sat)
(exit)
