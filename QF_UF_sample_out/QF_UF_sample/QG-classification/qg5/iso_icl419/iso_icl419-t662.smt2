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
(assert (= (= e1 (op e4 e4)) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (= e1 (op e4 e3)) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) e3))))
(assert (= (= e1 (op e4 e2)) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3)))))
(assert (= (= e1 (op e4 e0)) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 e3)))))
(assert (= (= e1 (op e4 e1)) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op e3 e3))))))
(assert (not (= (or (= e1 (op e4 e4)) (= e1 (op e4 e3)) (= e1 (op e4 e2)) (= e1 (op e4 e0)) (= e1 (op e4 e1))) (or (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) e3)) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 e3))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op e3 e3))))))))
(check-sat)
(exit)
