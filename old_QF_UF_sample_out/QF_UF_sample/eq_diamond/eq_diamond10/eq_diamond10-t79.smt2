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
(assert (and (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1))) (or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2))) (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (or (and (= x5 y5) (= y5 x6)) (and (= x5 z5) (= z5 x6))) (or (and (= x6 y6) (= y6 x7)) (and (= x6 z6) (= z6 x7))) (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))) (not (= x0 x9))))
(assert (not (or (and (= x6 y6) (= y6 x7)) (and (= x6 z6) (= z6 x7)))))
(check-sat)
(exit)
