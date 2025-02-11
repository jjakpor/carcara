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
(assert (or (= x0 x1) (not (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1))))))
(assert (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1))))
(assert (not (= x0 x1)))
(check-sat)
(exit)
