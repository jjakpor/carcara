(set-logic QF_UF)
(declare-sort MODE 0)
(declare-sort Z 0)
(declare-fun i1 () Bool)
(declare-fun i2 () Bool)
(declare-fun p2 () Bool)
(declare-fun a1 () Z)
(declare-fun a2 () Z)
(declare-fun b1 () Z)
(declare-fun b2 () Z)
(declare-fun cir () MODE)
(declare-fun mode () MODE)
(declare-fun r1 () Z)
(declare-fun r2 () Z)
(assert (or (not (= (not (= i2 (not (= r2 b2)))) (not (= i2 (not (= b2 r2)))))) (not (not (= i2 (not (= r2 b2))))) (not (= i2 (not (= b2 r2))))))
(assert (= (not (= i2 (not (= r2 b2)))) (not (= i2 (not (= b2 r2))))))
(assert (not (= i2 (not (= r2 b2)))))
(assert (not (not (= i2 (not (= b2 r2))))))
(check-sat)
(exit)
