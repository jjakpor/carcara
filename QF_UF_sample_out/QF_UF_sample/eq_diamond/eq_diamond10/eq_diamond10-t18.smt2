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
(assert (or (not (= (= (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (and (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (=> (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (= x3 x4)))) true)) (= (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (and (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (=> (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (= x3 x4))))))
(assert (= (= (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (and (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (=> (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (= x3 x4)))) true))
(assert (not (= (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (and (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (=> (or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4))) (= x3 x4))))))
(check-sat)
(exit)
