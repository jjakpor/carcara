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
(assert (not (not (= (or (or (or (or (= (op e2 e4) e0) (= (op e2 e4) e1)) (= (op e2 e4) e2)) (= (op e2 e4) e3)) (= (op e2 e4) e4)) (or (= (op e0 e0) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= (op (op (op e0 (op e0 e0)) e0) e0) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= (op (op e0 (op e0 e0)) e0) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= e0 (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= (op e0 (op e0 e0)) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))))))))
(assert (not (not (or (or (or (or (= (op e2 e4) e0) (= (op e2 e4) e1)) (= (op e2 e4) e2)) (= (op e2 e4) e3)) (= (op e2 e4) e4)))))
(assert (not (or (= (op e0 e0) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= (op (op (op e0 (op e0 e0)) e0) e0) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= (op (op e0 (op e0 e0)) e0) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= e0 (op (op (op e0 (op e0 e0)) e0) (op e0 e0))) (= (op e0 (op e0 e0)) (op (op (op e0 (op e0 e0)) e0) (op e0 e0))))))
(check-sat)
(exit)
