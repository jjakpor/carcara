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
(assert (and (and (and (and (not (= (op e0 e3) (op e1 e3))) (not (= (op e0 e3) (op e2 e3)))) (not (= (op e0 e3) (op e3 e3)))) (not (= (op e0 e3) (op e4 e3)))) (not (= (op e1 e3) (op e2 e3)))))
(assert (not (and (and (and (not (= (op e0 e3) (op e1 e3))) (not (= (op e0 e3) (op e2 e3)))) (not (= (op e0 e3) (op e3 e3)))) (not (= (op e0 e3) (op e4 e3))))))
(check-sat)
(exit)
