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
(assert (not (and (= e5 (op e5 e0)) (= e0 (op e5 (op e5 e0))))))
(assert (not (not (= e5 (op e5 e0)))))
(assert (not (not (= e0 (op e5 (op e5 e0))))))
(check-sat)
(exit)
