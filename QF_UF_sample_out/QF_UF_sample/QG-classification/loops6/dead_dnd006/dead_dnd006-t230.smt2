(set-logic QF_UF)
(declare-sort U 0)
(declare-sort I 0)
(declare-fun unit () I)
(declare-fun op (I I) I)
(declare-fun e5 () I)
(declare-fun e4 () I)
(declare-fun e3 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)
(assert (or (not (= e4 (op e4 e0))) (not (= e0 (op e4 (op e4 e0)))) (= e4 (op e4 (op e4 e4)))))
(assert (not (not (= e0 (op e4 (op e4 e0))))))
(assert (not (= e4 (op e4 (op e4 e4)))))
(assert (not (not (= e4 (op e4 e0)))))
(check-sat)
(exit)
