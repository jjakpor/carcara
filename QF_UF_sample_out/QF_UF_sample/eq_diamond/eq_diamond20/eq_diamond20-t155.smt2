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
(declare-fun x15 () U)
(declare-fun y15 () U)
(declare-fun z15 () U)
(declare-fun x16 () U)
(declare-fun y16 () U)
(declare-fun z16 () U)
(declare-fun x17 () U)
(declare-fun y17 () U)
(declare-fun z17 () U)
(declare-fun x18 () U)
(declare-fun y18 () U)
(declare-fun z18 () U)
(declare-fun x19 () U)
(declare-fun y19 () U)
(declare-fun z19 () U)
(assert (or (not (= (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (and (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (=> (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (= x13 x14))))) (not (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14)))) (and (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (=> (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (= x13 x14)))))
(assert (= (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (and (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (=> (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (= x13 x14)))))
(assert (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))))
(assert (not (and (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (=> (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (= x13 x14)))))
(check-sat)
(exit)
