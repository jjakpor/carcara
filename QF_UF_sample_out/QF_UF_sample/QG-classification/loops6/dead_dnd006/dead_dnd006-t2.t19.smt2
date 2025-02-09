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
(assert (= e1 e1))
(assert (= e0 (op e1 e1)))
(assert (not (= (op e1 e0) (op e1 (op e1 e1)))))
(check-sat)
(exit)
