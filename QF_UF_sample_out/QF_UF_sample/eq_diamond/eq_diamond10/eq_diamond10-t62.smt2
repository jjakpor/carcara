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
(declare-fun x4 () U)
(declare-fun y4 () U)
(declare-fun z4 () U)
(declare-fun x5 () U)
(declare-fun y5 () U)
(declare-fun z5 () U)
(declare-fun x6 () U)
(declare-fun y6 () U)
(declare-fun z6 () U)
(declare-fun x7 () U)
(declare-fun y7 () U)
(declare-fun z7 () U)
(declare-fun x8 () U)
(declare-fun y8 () U)
(declare-fun z8 () U)
(declare-fun x9 () U)
(declare-fun y9 () U)
(declare-fun z9 () U)
(assert (= x4 x3))
(assert (= x3 x2))
(assert (= x2 x1))
(assert (= x1 x0))
(assert (not (= x4 x0)))
(check-sat)
(exit)
