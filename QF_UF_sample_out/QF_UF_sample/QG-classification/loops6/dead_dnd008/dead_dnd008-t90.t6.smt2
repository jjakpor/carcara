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
(assert (and (and (and (and (and (and (and (= (op unit e0) e0) (= (op e0 unit) e0)) (and (= (op unit e1) e1) (= (op e1 unit) e1))) (and (= (op unit e2) e2) (= (op e2 unit) e2))) (and (= (op unit e3) e3) (= (op e3 unit) e3))) (and (= (op unit e4) e4) (= (op e4 unit) e4))) (and (= (op unit e5) e5) (= (op e5 unit) e5))) (or (or (or (or (or (= unit e0) (= unit e1)) (= unit e2)) (= unit e3)) (= unit e4)) (= unit e5))))
(assert (not (and (and (and (and (and (and (= (op unit e0) e0) (= (op e0 unit) e0)) (and (= (op unit e1) e1) (= (op e1 unit) e1))) (and (= (op unit e2) e2) (= (op e2 unit) e2))) (and (= (op unit e3) e3) (= (op e3 unit) e3))) (and (= (op unit e4) e4) (= (op e4 unit) e4))) (and (= (op unit e5) e5) (= (op e5 unit) e5)))))
(check-sat)
(exit)
