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
(assert (or (not (= (not (= (op e2 e4) (op e4 e4))) (not (= (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))) (not (not (= (op e2 e4) (op e4 e4)))) (not (= (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))))))
(assert (= (not (= (op e2 e4) (op e4 e4))) (not (= (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))))))
(assert (not (= (op e2 e4) (op e4 e4))))
(assert (not (not (= (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))))))
(check-sat)
(exit)
