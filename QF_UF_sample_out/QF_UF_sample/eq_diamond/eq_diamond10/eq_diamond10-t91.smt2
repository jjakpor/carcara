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
(assert (or (not (= (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (and (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (=> (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (= x7 x8))))) (not (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8)))) (and (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (=> (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (= x7 x8)))))
(assert (= (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (and (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (=> (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (= x7 x8)))))
(assert (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))))
(assert (not (and (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (=> (or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8))) (= x7 x8)))))
(check-sat)
(exit)
