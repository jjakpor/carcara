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
(assert (= (not (and (= e0 (op e4 e4)) (= e1 (op e4 e3)) (= e2 (op e4 e2)) (= e3 (op e4 e1)) (= e4 (op e4 e0)) (= e2 (op e3 e4)) (= e3 (op e3 e3)) (= e4 (op e3 e2)) (= e0 (op e3 e1)) (= e1 (op e3 e0)) (= e4 (op e2 e4)) (= e0 (op e2 e3)) (= e1 (op e2 e2)) (= e2 (op e2 e1)) (= e3 (op e2 e0)) (= e1 (op e1 e4)) (= e2 (op e1 e3)) (= e3 (op e1 e2)) (= e4 (op e1 e1)) (= e0 (op e1 e0)) (= e3 (op e0 e4)) (= e4 (op e0 e3)) (= e0 (op e0 e2)) (= e2 (op e0 e0)) (= e1 (op e0 e1)))) (not (and (= e0 (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) e0))) (= (op e0 e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 e0))) (= (op (op e0 e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op e0 e0) e0) (op (op (op e0 e0) e0) (op (op e0 e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) (op e0 e0))) (= e0 (op (op (op e0 e0) e0) (op (op (op e0 e0) e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= e0 (op (op e0 e0) (op (op e0 e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op e0 e0) (op e0 e0))) (= (op e0 e0) (op (op e0 e0) (op (op (op e0 e0) e0) e0))) (= (op (op e0 e0) e0) (op (op e0 e0) e0)) (= (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op e0 e0) e0))) (= (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op e0 e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0))) (= e0 (op (op (op (op e0 e0) e0) e0) e0)) (= (op (op e0 e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 (op (op e0 e0) e0))) (= e0 (op e0 (op e0 e0))) (= (op e0 e0) (op e0 e0)) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0)))))))
(assert (= (not (and (= e0 (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) e0))) (= (op e0 e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 e0))) (= (op (op e0 e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op e0 e0) e0) (op (op (op e0 e0) e0) (op (op e0 e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) (op e0 e0))) (= e0 (op (op (op e0 e0) e0) (op (op (op e0 e0) e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= e0 (op (op e0 e0) (op (op e0 e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op e0 e0) (op e0 e0))) (= (op e0 e0) (op (op e0 e0) (op (op (op e0 e0) e0) e0))) (= (op (op e0 e0) e0) (op (op e0 e0) e0)) (= (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op e0 e0) e0))) (= (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op e0 e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0))) (= e0 (op (op (op (op e0 e0) e0) e0) e0)) (= (op (op e0 e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 (op (op e0 e0) e0))) (= e0 (op e0 (op e0 e0))) (= (op e0 e0) (op e0 e0)) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0))))) (not (and (= e0 (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) e0))) (= (op e0 e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 e0))) (= (op (op e0 e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op e0 e0) e0) (op (op (op e0 e0) e0) (op (op e0 e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) (op e0 e0))) (= e0 (op (op (op e0 e0) e0) (op (op (op e0 e0) e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= e0 (op (op e0 e0) (op (op e0 e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op e0 e0) (op e0 e0))) (= (op e0 e0) (op (op e0 e0) (op (op (op e0 e0) e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op e0 e0) e0))) (= (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op e0 e0))) (= e0 (op (op (op (op e0 e0) e0) e0) e0)) (= (op (op e0 e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 (op (op e0 e0) e0))) (= e0 (op e0 (op e0 e0))) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0)))))))
(assert (not (= (not (and (= e0 (op e4 e4)) (= e1 (op e4 e3)) (= e2 (op e4 e2)) (= e3 (op e4 e1)) (= e4 (op e4 e0)) (= e2 (op e3 e4)) (= e3 (op e3 e3)) (= e4 (op e3 e2)) (= e0 (op e3 e1)) (= e1 (op e3 e0)) (= e4 (op e2 e4)) (= e0 (op e2 e3)) (= e1 (op e2 e2)) (= e2 (op e2 e1)) (= e3 (op e2 e0)) (= e1 (op e1 e4)) (= e2 (op e1 e3)) (= e3 (op e1 e2)) (= e4 (op e1 e1)) (= e0 (op e1 e0)) (= e3 (op e0 e4)) (= e4 (op e0 e3)) (= e0 (op e0 e2)) (= e2 (op e0 e0)) (= e1 (op e0 e1)))) (not (and (= e0 (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op e0 e0) e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) e0))) (= (op e0 e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 e0))) (= (op (op e0 e0) e0) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) e0)) (= (op e0 e0) (op (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op e0 e0) e0) (op (op (op e0 e0) e0) (op (op e0 e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op (op e0 e0) e0) (op e0 e0))) (= e0 (op (op (op e0 e0) e0) (op (op (op e0 e0) e0) e0))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= e0 (op (op e0 e0) (op (op e0 e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op e0 e0) (op e0 e0))) (= (op e0 e0) (op (op e0 e0) (op (op (op e0 e0) e0) e0))) (= (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op e0 e0) (op (op (op (op e0 e0) e0) e0) (op (op e0 e0) e0))) (= (op (op e0 e0) e0) (op (op (op (op e0 e0) e0) e0) (op e0 e0))) (= e0 (op (op (op (op e0 e0) e0) e0) e0)) (= (op (op e0 e0) e0) (op e0 (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)))) (= (op (op (op (op e0 e0) e0) e0) (op (op (op e0 e0) e0) e0)) (op e0 (op (op e0 e0) e0))) (= e0 (op e0 (op e0 e0))) (= (op (op (op e0 e0) e0) e0) (op e0 (op (op (op e0 e0) e0) e0))))))))
(check-sat)
(exit)
