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
(assert (= (or (or (or (or (= (op e0 e2) e4) (= (op e1 e2) e4)) (= (op e2 e2) e4)) (= (op e3 e2) e4)) (= (op e4 e2) e4)) (or (= (op e4 e2) e4) (= (op e3 e2) e4) (= (op e2 e2) e4) (= (op e0 e2) e4) (= (op e1 e2) e4))))
(assert (= (or (= (op e4 e2) e4) (= (op e3 e2) e4) (= (op e2 e2) e4) (= (op e0 e2) e4) (= (op e1 e2) e4)) (or (= e4 (op e4 e2)) (= e4 (op e3 e2)) (= e4 (op e2 e2)) (= e4 (op e0 e2)) (= e4 (op e1 e2)))))
(assert (not (= (or (or (or (or (= (op e0 e2) e4) (= (op e1 e2) e4)) (= (op e2 e2) e4)) (= (op e3 e2) e4)) (= (op e4 e2) e4)) (or (= e4 (op e4 e2)) (= e4 (op e3 e2)) (= e4 (op e2 e2)) (= e4 (op e0 e2)) (= e4 (op e1 e2))))))
(check-sat)
(exit)
