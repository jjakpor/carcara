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
(assert (not (not (= (or (or (or (or (= (op e0 e3) e0) (= (op e1 e3) e0)) (= (op e2 e3) e0)) (= (op e3 e3) e0)) (= (op e4 e3) e0)) (or (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op (op e1 e1) (op e1 (op e1 e1))) (op e1 (op e1 e1)))) (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op e1 (op e1 e1)) (op e1 (op e1 e1)))) (= (op (op e1 e1) (op e1 (op e1 e1))) (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1))))) (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op e1 (op e1 e1)))) (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op e1 (op e1 (op e1 e1)))))))))
(assert (not (not (or (or (or (or (= (op e0 e3) e0) (= (op e1 e3) e0)) (= (op e2 e3) e0)) (= (op e3 e3) e0)) (= (op e4 e3) e0)))))
(assert (not (or (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op (op e1 e1) (op e1 (op e1 e1))) (op e1 (op e1 e1)))) (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op e1 (op e1 e1)) (op e1 (op e1 e1)))) (= (op (op e1 e1) (op e1 (op e1 e1))) (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1))))) (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op e1 (op e1 e1)))) (= (op (op (op e1 e1) (op e1 (op e1 e1))) (op (op e1 e1) (op e1 (op e1 e1)))) (op e1 (op e1 (op e1 e1)))))))
(check-sat)
(exit)
