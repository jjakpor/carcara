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
(assert (or (not (= (not (= (op e0 e0) (op e0 e4))) (not (= (op (op (op e4 e3) (op e4 e3)) (op (op e4 e3) (op e4 e3))) (op (op (op e4 e3) (op e4 e3)) e4))))) (not (not (= (op e0 e0) (op e0 e4)))) (not (= (op (op (op e4 e3) (op e4 e3)) (op (op e4 e3) (op e4 e3))) (op (op (op e4 e3) (op e4 e3)) e4)))))
(assert (= (not (= (op e0 e0) (op e0 e4))) (not (= (op (op (op e4 e3) (op e4 e3)) (op (op e4 e3) (op e4 e3))) (op (op (op e4 e3) (op e4 e3)) e4)))))
(assert (not (= (op e0 e0) (op e0 e4))))
(assert (not (not (= (op (op (op e4 e3) (op e4 e3)) (op (op e4 e3) (op e4 e3))) (op (op (op e4 e3) (op e4 e3)) e4)))))
(check-sat)
(exit)
