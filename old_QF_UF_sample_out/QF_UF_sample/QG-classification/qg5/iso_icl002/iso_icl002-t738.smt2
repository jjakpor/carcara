(set-logic QF_UF)
(declare-sort U 0)
(declare-sort I 0)
(declare-fun op1 (I I) I)
(declare-fun op (I I) I)
(declare-fun e4 () I)
(declare-fun e3 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)
(assert (not (not (= (not (= (op e0 e3) (op e2 e3))) (not (= (op e0 (op (op (op e0 (op e0 e0)) e0) e0)) (op (op (op e0 (op e0 e0)) e0) (op (op (op e0 (op e0 e0)) e0) e0))))))))
(assert (not (not (not (= (op e0 e3) (op e2 e3))))))
(assert (not (not (= (op e0 (op (op (op e0 (op e0 e0)) e0) e0)) (op (op (op e0 (op e0 e0)) e0) (op (op (op e0 (op e0 e0)) e0) e0))))))
(check-sat)
(exit)
