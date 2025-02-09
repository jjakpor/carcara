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
(assert (or (not (= e3 (op e3 e0))) (not (= e0 (op e3 (op e3 e0)))) (= e3 (op e3 (op e3 e3)))))
(assert (not (= e3 (op e3 (op e3 e3)))))
(assert (not (not (= e3 (op e3 e0)))))
(assert (not (not (= e0 (op e3 (op e3 e0))))))
(check-sat)
(exit)
