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
(assert (or (not (and (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3)))) (= e1 (op e3 (op (op e1 e3) e3))))) (not (and (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3)))) (= e1 (op e3 (op (op e1 e3) e3))))) (= (op e3 e1) (op (op e1 e3) e3))))
(assert (not (not (and (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3)))) (= e1 (op e3 (op (op e1 e3) e3)))))))
(assert (not (= (op e3 e1) (op (op e1 e3) e3))))
(check-sat)
(exit)
