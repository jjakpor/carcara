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
(declare-fun x10 () U)
(declare-fun y10 () U)
(declare-fun z10 () U)
(declare-fun x11 () U)
(declare-fun y11 () U)
(declare-fun z11 () U)
(declare-fun x12 () U)
(declare-fun y12 () U)
(declare-fun z12 () U)
(declare-fun x13 () U)
(declare-fun y13 () U)
(declare-fun z13 () U)
(declare-fun x14 () U)
(declare-fun y14 () U)
(declare-fun z14 () U)
(assert (= (= (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3)))) true) (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3))))))
(assert (not (not (= (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3)))) true))))
(assert (not (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3))))))
(check-sat)
(exit)
