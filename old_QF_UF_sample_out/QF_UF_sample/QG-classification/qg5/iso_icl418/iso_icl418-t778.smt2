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
(assert (and (or (or (or (or (= (op e2 e0) e0) (= (op e2 e1) e0)) (= (op e2 e2) e0)) (= (op e2 e3) e0)) (= (op e2 e4) e0)) (or (or (or (or (= (op e0 e2) e0) (= (op e1 e2) e0)) (= (op e2 e2) e0)) (= (op e3 e2) e0)) (= (op e4 e2) e0))))
(assert (not (or (or (or (or (= (op e0 e2) e0) (= (op e1 e2) e0)) (= (op e2 e2) e0)) (= (op e3 e2) e0)) (= (op e4 e2) e0))))
(check-sat)
(exit)
