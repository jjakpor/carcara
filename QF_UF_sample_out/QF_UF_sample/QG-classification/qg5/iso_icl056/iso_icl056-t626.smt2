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
(assert (not (= (= (= (op (op e1 e1) (op e1 (op e1 e1))) (op (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op e1 e1) (op e1 (op e1 e1))))) false) (not (= (op (op e1 e1) (op e1 (op e1 e1))) (op (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op e1 e1) (op e1 (op e1 e1)))))))))
(check-sat)
(exit)
