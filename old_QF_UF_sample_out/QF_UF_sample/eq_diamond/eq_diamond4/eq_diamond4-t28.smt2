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
(assert (= (= (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3)))) true) (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3))))))
(assert (not (not (= (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3)))) true))))
(assert (not (= (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (and (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (=> (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (= x2 x3))))))
(check-sat)
(exit)
