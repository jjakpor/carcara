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
(assert (= (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) e3)) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) e3))))
(assert (= (= e3 (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (= e3 (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3)))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op e3 e3)))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op e3 e3))))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 e3))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 e3)))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) e3) (op e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (= (op e3 e3) (op e3 e3)) true))
(assert (= (= (op (op e3 e3) (op e3 e3)) (op e3 (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op e3 e3) (op e3 e3)) (op e3 (op (op (op e3 e3) (op e3 e3)) e3)))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 (op (op e3 e3) (op e3 e3)))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 (op (op e3 e3) (op e3 e3))))))
(assert (= (= e3 (op e3 (op e3 e3))) (= e3 (op e3 (op e3 e3)))))
(assert (= (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) e3)) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) e3))))
(assert (= (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) e3))) (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) e3)))))
(assert (= (= e3 (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op e3 e3)))) (= e3 (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op e3 e3))))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op e3 e3))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op e3 e3)))))
(assert (= (= e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) e3)) true))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))) true))
(assert (= (= (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op e3 e3) (op e3 e3)))) (= (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op e3 e3) (op e3 e3))))))
(assert (= (= (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op e3 e3))) (= (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op e3 e3)))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))))))
(assert (= (= e3 (op (op e3 e3) e3)) (= e3 (op (op e3 e3) e3))))
(assert (= (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) e3)))))
(assert (= (= (op (op e3 e3) (op e3 e3)) (op (op e3 e3) (op e3 e3))) true))
(assert (= (= (op e3 e3) (op (op e3 e3) (op (op e3 e3) (op e3 e3)))) (= (op e3 e3) (op (op e3 e3) (op (op e3 e3) (op e3 e3))))))
(assert (not (= (and (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) e3)) (= e3 (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op e3 e3)))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 e3))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op e3 e3) (op e3 e3)) (= (op (op e3 e3) (op e3 e3)) (op e3 (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 (op (op e3 e3) (op e3 e3)))) (= e3 (op e3 (op e3 e3))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) e3)) (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) e3))) (= e3 (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op e3 e3)))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op e3 e3))) (= e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) e3)) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op e3 e3) (op e3 e3)))) (= (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op e3 e3))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= e3 (op (op e3 e3) e3)) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op e3 e3) (op e3 e3)) (op (op e3 e3) (op e3 e3))) (= (op e3 e3) (op (op e3 e3) (op (op e3 e3) (op e3 e3))))) (and (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) e3)) (= e3 (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op e3 e3)))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 e3))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) true (= (op (op e3 e3) (op e3 e3)) (op e3 (op (op (op e3 e3) (op e3 e3)) e3))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op e3 (op (op e3 e3) (op e3 e3)))) (= e3 (op e3 (op e3 e3))) (= (op (op e3 e3) (op e3 e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op (op (op e3 e3) (op e3 e3)) e3) e3)) (= (op e3 e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op e3 e3) (op e3 e3)) e3))) (= e3 (op (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op e3 e3)))) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op (op (op e3 e3) (op e3 e3)) e3) (op e3 e3))) (= e3 (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) true true (= (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) (op (op e3 e3) (op e3 e3)))) (= (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op e3 e3))) (= (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) (op (op (op e3 e3) (op e3 e3)) e3)))) (= e3 (op (op e3 e3) e3)) (= (op (op (op e3 e3) (op e3 e3)) e3) (op (op e3 e3) (op (op (op e3 e3) (op e3 e3)) e3))) true (= (op e3 e3) (op (op e3 e3) (op (op e3 e3) (op e3 e3))))))))
(check-sat)
(exit)
