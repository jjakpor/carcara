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
(assert (or (not (= (= (op (op e4 e2) e4) e2) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))))) (not (= (op (op e4 e2) e4) e2)) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (= (op (op e4 e2) e4) e2) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (op (op e4 e2) e4) e2))
(assert (not (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(check-sat)
(exit)
