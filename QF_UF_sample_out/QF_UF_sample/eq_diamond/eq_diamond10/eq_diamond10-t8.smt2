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
(assert (or (not (= (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (and (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (=> (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (= x4 x5))))) (not (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5)))) (and (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (=> (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (= x4 x5)))))
(assert (= (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (and (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (=> (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (= x4 x5)))))
(assert (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))))
(assert (not (and (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (=> (or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5))) (= x4 x5)))))
(check-sat)
(exit)
