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
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (= e0 e1)) (not (= e0 e2))) (not (= e0 e3))) (not (= e0 e4))) (not (= e0 e5))) (not (= e1 e2))) (not (= e1 e3))) (not (= e1 e4))) (not (= e1 e5))) (not (= e2 e3))) (not (= e2 e4))) (not (= e2 e5))) (not (= e3 e4))) (not (= e3 e5))) (not (= e4 e5))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (not (= e0 e1)) (not (= e0 e2))) (not (= e0 e3))) (not (= e0 e4))) (not (= e0 e5))) (not (= e1 e2))) (not (= e1 e3))) (not (= e1 e4))) (not (= e1 e5))) (not (= e2 e3))) (not (= e2 e4))) (not (= e2 e5))) (not (= e3 e4))) (not (= e3 e5)))))
(check-sat)
(exit)
