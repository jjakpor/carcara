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
(assert (or (not (= (or (or (or (or (= (op e0 e0) e1) (= (op e0 e1) e1)) (= (op e0 e2) e1)) (= (op e0 e3) e1)) (= (op e0 e4) e1)) (or (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op e0 e0) e0))) (= (op e0 (op e0 e0)) (op (op (op e0 e0) e0) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) e0)) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0)))))) (not (or (or (or (or (= (op e0 e0) e1) (= (op e0 e1) e1)) (= (op e0 e2) e1)) (= (op e0 e3) e1)) (= (op e0 e4) e1))) (or (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op e0 e0) e0))) (= (op e0 (op e0 e0)) (op (op (op e0 e0) e0) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) e0)) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0))))))
(assert (= (or (or (or (or (= (op e0 e0) e1) (= (op e0 e1) e1)) (= (op e0 e2) e1)) (= (op e0 e3) e1)) (= (op e0 e4) e1)) (or (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op e0 e0) e0))) (= (op e0 (op e0 e0)) (op (op (op e0 e0) e0) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) e0)) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0))))))
(assert (or (or (or (or (= (op e0 e0) e1) (= (op e0 e1) e1)) (= (op e0 e2) e1)) (= (op e0 e3) e1)) (= (op e0 e4) e1)))
(assert (not (or (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op e0 e0) e0))) (= (op e0 (op e0 e0)) (op (op (op e0 e0) e0) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) e0)) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0))))))
(check-sat)
(exit)
