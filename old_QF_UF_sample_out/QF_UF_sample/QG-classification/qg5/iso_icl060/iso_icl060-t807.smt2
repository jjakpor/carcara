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
(assert (or (not (= (or (not (not (= (op e3 e1) (op e3 e3)))) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1))))) (or (= (op e3 e1) (op e3 e3)) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1))))))) (not (or (not (not (= (op e3 e1) (op e3 e3)))) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1)))))) (or (= (op e3 e1) (op e3 e3)) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1)))))))
(assert (= (or (not (not (= (op e3 e1) (op e3 e3)))) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1))))) (or (= (op e3 e1) (op e3 e3)) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1)))))))
(assert (or (not (not (= (op e3 e1) (op e3 e3)))) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1))))))
(assert (not (or (= (op e3 e1) (op e3 e3)) (not (= e1 (op e3 (op (op e1 e3) e3)))) (not (= (op (op e1 e3) e3) (op e3 (op e3 (op (op e1 e3) e3))))) (not (= e3 (op e3 e3))) (not (= e3 (op (op e1 e3) (op (op e1 e3) e3)))) (not (= e3 (op (op (op e1 e3) e3) (op (op (op e1 e3) e3) e3)))) (not (= (op (op e1 e3) e1) (op (op (op e1 e3) e3) e3))) (not (= (op (op e1 e3) e3) (op (op (op e1 e3) e3) (op (op e1 e3) e1)))))))
(check-sat)
(exit)
