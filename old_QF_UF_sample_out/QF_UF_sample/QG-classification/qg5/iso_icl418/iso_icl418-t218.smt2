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
(assert (or (not (= (or (not (= (op e1 e0) e1)) (= (op e0 e1) e1)) (or (not (= (op e4 e3) (op (op e4 e3) (op (op e4 e3) (op e4 e3))))) (= (op e4 e3) (op (op (op e4 e3) (op e4 e3)) (op e4 e3)))))) (not (or (not (= (op e1 e0) e1)) (= (op e0 e1) e1))) (or (not (= (op e4 e3) (op (op e4 e3) (op (op e4 e3) (op e4 e3))))) (= (op e4 e3) (op (op (op e4 e3) (op e4 e3)) (op e4 e3))))))
(assert (= (or (not (= (op e1 e0) e1)) (= (op e0 e1) e1)) (or (not (= (op e4 e3) (op (op e4 e3) (op (op e4 e3) (op e4 e3))))) (= (op e4 e3) (op (op (op e4 e3) (op e4 e3)) (op e4 e3))))))
(assert (or (not (= (op e1 e0) e1)) (= (op e0 e1) e1)))
(assert (not (or (not (= (op e4 e3) (op (op e4 e3) (op (op e4 e3) (op e4 e3))))) (= (op e4 e3) (op (op (op e4 e3) (op e4 e3)) (op e4 e3))))))
(check-sat)
(exit)
