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
(assert (= (= e4 (op e0 e3)) (= (op e0 e0) (op e0 (op (op (op e0 (op e0 e0)) e0) e0)))))
(assert (= (= e3 (op e0 e3)) (= (op (op (op e0 (op e0 e0)) e0) e0) (op e0 (op (op (op e0 (op e0 e0)) e0) e0)))))
(assert (= (= e2 (op e0 e3)) (= (op (op e0 (op e0 e0)) e0) (op e0 (op (op (op e0 (op e0 e0)) e0) e0)))))
(assert (= (= e0 (op e0 e3)) (= e0 (op e0 (op (op (op e0 (op e0 e0)) e0) e0)))))
(assert (= (= e1 (op e0 e3)) (= (op e0 (op e0 e0)) (op e0 (op (op (op e0 (op e0 e0)) e0) e0)))))
(assert (not (= (or (= e4 (op e0 e3)) (= e3 (op e0 e3)) (= e2 (op e0 e3)) (= e0 (op e0 e3)) (= e1 (op e0 e3))) (or (= (op e0 e0) (op e0 (op (op (op e0 (op e0 e0)) e0) e0))) (= (op (op (op e0 (op e0 e0)) e0) e0) (op e0 (op (op (op e0 (op e0 e0)) e0) e0))) (= (op (op e0 (op e0 e0)) e0) (op e0 (op (op (op e0 (op e0 e0)) e0) e0))) (= e0 (op e0 (op (op (op e0 (op e0 e0)) e0) e0))) (= (op e0 (op e0 e0)) (op e0 (op (op (op e0 (op e0 e0)) e0) e0)))))))
(check-sat)
(exit)
