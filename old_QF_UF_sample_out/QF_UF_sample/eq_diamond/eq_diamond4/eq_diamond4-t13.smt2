(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x0 () U)
(declare-fun y0 () U)
(declare-fun z0 () U)
(declare-fun x1 () U)
(declare-fun y1 () U)
(declare-fun z1 () U)
(declare-fun x2 () U)
(declare-fun y2 () U)
(declare-fun z2 () U)
(declare-fun x3 () U)
(declare-fun y3 () U)
(declare-fun z3 () U)
(assert (= (= (= x1 x2) false) (not (= x1 x2))))
(assert (not (not (= (= x1 x2) false))))
(assert (not (not (= x1 x2))))
(check-sat)
(exit)
