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
(assert (= (= e4 (op e3 e4)) (= (op (op e1 e1) (op e1 e1)) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1))))))
(assert (= (= e3 (op e3 e4)) (= (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1))))))
(assert (= (= e2 (op e3 e4)) (= (op e1 e1) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1))))))
(assert (= (= e0 (op e3 e4)) (= (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1))) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1))))))
(assert (= (= e1 (op e3 e4)) (= e1 (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1))))))
(assert (not (= (or (= e4 (op e3 e4)) (= e3 (op e3 e4)) (= e2 (op e3 e4)) (= e0 (op e3 e4)) (= e1 (op e3 e4))) (or (= (op (op e1 e1) (op e1 e1)) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1)))) (= (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1)))) (= (op e1 e1) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1)))) (= (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1))) (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1)))) (= e1 (op (op (op e1 e1) (op (op (op e1 e1) (op e1 e1)) (op (op e1 e1) (op e1 e1)))) (op (op e1 e1) (op e1 e1))))))))
(check-sat)
(exit)
