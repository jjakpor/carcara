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
(assert (and (and (not (= (op e0 e4) (op e1 e4))) (not (= (op e0 e4) (op e2 e4)))) (not (= (op e0 e4) (op e3 e4)))))
(assert (not (and (not (= (op e0 e4) (op e1 e4))) (not (= (op e0 e4) (op e2 e4))))))
(check-sat)
(exit)
