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
(assert (not (not (= (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))) (and (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))) (=> (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))) (= x8 x9)))))))
(assert (not (not (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))))))
(assert (not (and (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))) (=> (or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9))) (= x8 x9)))))
(check-sat)
(exit)
