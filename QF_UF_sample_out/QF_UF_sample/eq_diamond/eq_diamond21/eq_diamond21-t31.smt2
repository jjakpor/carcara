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
(declare-fun x20 () U)
(declare-fun y20 () U)
(declare-fun z20 () U)
(assert (and (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1))) (or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2))) (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (or (and (= x5 y5) (= y5 x6)) (and (= x5 z5) (= z5 x6))) (or (and (= x6 y6) (= y6 x7)) (and (= x6 z6) (= z6 x7))) (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))) (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (or (and (= x10 y10) (= y10 x11)) (and (= x10 z10) (= z10 x11))) (or (and (= x11 y11) (= y11 x12)) (and (= x11 z11) (= z11 x12))) (or (and (= x12 y12) (= y12 x13)) (and (= x12 z12) (= z12 x13))) (or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14))) (or (and (= x14 y14) (= y14 x15)) (and (= x14 z14) (= z14 x15))) (or (and (= x15 y15) (= y15 x16)) (and (= x15 z15) (= z15 x16))) (or (and (= x16 y16) (= y16 x17)) (and (= x16 z16) (= z16 x17))) (or (and (= x17 y17) (= y17 x18)) (and (= x17 z17) (= z17 x18))) (or (and (= x18 y18) (= y18 x19)) (and (= x18 z18) (= z18 x19))) (or (and (= x19 y19) (= y19 x20)) (and (= x19 z19) (= z19 x20))) (not (= x0 x20))))
(assert (not (or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2)))))
(check-sat)
(exit)
