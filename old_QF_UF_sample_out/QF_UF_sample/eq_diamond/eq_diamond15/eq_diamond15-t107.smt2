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
(assert (= (= (= (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (and (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (=> (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (= x9 x10)))) true) (= (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (and (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (=> (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (= x9 x10))))))
(assert (not (not (= (= (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (and (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (=> (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (= x9 x10)))) true))))
(assert (not (= (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (and (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (=> (or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10))) (= x9 x10))))))
(check-sat)
(exit)
