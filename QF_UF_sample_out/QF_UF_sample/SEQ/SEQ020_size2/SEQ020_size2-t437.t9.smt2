(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p3 (U) Bool)
(declare-fun p1 (U U) Bool)
(declare-fun p4 (U) Bool)
(declare-fun p14 (U U U) Bool)
(declare-fun p9 (U) Bool)
(declare-fun f12 (U) U)
(declare-fun f6 (U) U)
(declare-fun f2 (U U) U)
(declare-fun f17 (U U U) U)
(declare-fun p10 (U U) Bool)
(declare-fun f16 (U U U) U)
(declare-fun f7 (U) U)
(declare-fun f13 (U U U) U)
(declare-fun c18 () U)
(declare-fun f11 (U) U)
(declare-fun f5 (U) U)
(declare-fun c8 () U)
(declare-fun p15 (U U) Bool)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(assert (= c_0 (f7 c_1)))
(assert (not (= (f7 c_1) c_0)))
(check-sat)
(exit)
