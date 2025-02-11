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
(assert (and (and (= e0 (op e1 e1)) (= e1 (op e4 e3))) (= e2 (op e3 e4))))
(assert (not (and (= e0 (op e1 e1)) (= e1 (op e4 e3)))))
(check-sat)
(exit)
