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
(assert (and (distinct c_0 c_1) (or (not (p3 c_0)) (not (p1 c_0 c_0)) (= c_0 c_0) (p1 c_0 c_0) (not (p3 c_0)) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_0)) (not (p4 c_0)) (= c_0 c_0) (not (p14 c_0 c_0 c_0))) (or (not (p3 c_0)) (not (p1 c_0 c_0)) (= c_0 c_1) (p1 c_1 c_0) (not (p3 c_0)) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_0 c_0)) (not (p4 c_0)) (= c_0 c_0) (not (p14 c_0 c_0 c_1))) (or (not (p3 c_0)) (not (p1 c_0 c_1)) (= c_0 c_0) (p1 c_0 c_1) (not (p3 c_0)) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_1)) (not (p4 c_1)) (= c_0 c_0) (not (p14 c_0 c_0 c_0))) (or (not (p3 c_0)) (not (p1 c_0 c_1)) (= c_0 c_1) (p1 c_1 c_1) (not (p3 c_0)) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_0 c_1)) (not (p4 c_1)) (= c_0 c_0) (not (p14 c_0 c_0 c_1))) (or (not (p3 c_0)) (not (p1 c_1 c_0)) (= c_1 c_0) (p1 c_0 c_0) (not (p3 c_1)) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_0)) (not (p4 c_0)) (= c_1 c_0) (not (p14 c_1 c_0 c_0))) (or (not (p3 c_0)) (not (p1 c_1 c_0)) (= c_1 c_1) (p1 c_1 c_0) (not (p3 c_1)) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_0 c_0)) (not (p4 c_0)) (= c_1 c_0) (not (p14 c_1 c_0 c_1))) (or (not (p3 c_0)) (not (p1 c_1 c_1)) (= c_1 c_0) (p1 c_0 c_1) (not (p3 c_1)) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_1)) (not (p4 c_1)) (= c_1 c_0) (not (p14 c_1 c_0 c_0))) (or (not (p3 c_0)) (not (p1 c_1 c_1)) (= c_1 c_1) (p1 c_1 c_1) (not (p3 c_1)) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_0 c_1)) (not (p4 c_1)) (= c_1 c_0) (not (p14 c_1 c_0 c_1))) (or (not (p3 c_1)) (not (p1 c_0 c_0)) (= c_0 c_0) (p1 c_0 c_0) (not (p3 c_0)) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_1 c_0)) (not (p4 c_0)) (= c_0 c_1) (not (p14 c_0 c_1 c_0))) (or (not (p3 c_1)) (not (p1 c_0 c_0)) (= c_0 c_1) (p1 c_1 c_0) (not (p3 c_0)) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_0)) (not (p4 c_0)) (= c_0 c_1) (not (p14 c_0 c_1 c_1))) (or (not (p3 c_1)) (not (p1 c_0 c_1)) (= c_0 c_0) (p1 c_0 c_1) (not (p3 c_0)) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_1 c_1)) (not (p4 c_1)) (= c_0 c_1) (not (p14 c_0 c_1 c_0))) (or (not (p3 c_1)) (not (p1 c_0 c_1)) (= c_0 c_1) (p1 c_1 c_1) (not (p3 c_0)) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_1)) (not (p4 c_1)) (= c_0 c_1) (not (p14 c_0 c_1 c_1))) (or (not (p3 c_1)) (not (p1 c_1 c_0)) (= c_1 c_0) (p1 c_0 c_0) (not (p3 c_1)) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_1 c_0)) (not (p4 c_0)) (= c_1 c_1) (not (p14 c_1 c_1 c_0))) (or (not (p3 c_1)) (not (p1 c_1 c_0)) (= c_1 c_1) (p1 c_1 c_0) (not (p3 c_1)) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_0)) (not (p4 c_0)) (= c_1 c_1) (not (p14 c_1 c_1 c_1))) (or (not (p3 c_1)) (not (p1 c_1 c_1)) (= c_1 c_0) (p1 c_0 c_1) (not (p3 c_1)) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_1 c_1)) (not (p4 c_1)) (= c_1 c_1) (not (p14 c_1 c_1 c_0))) (or (not (p3 c_1)) (not (p1 c_1 c_1)) (= c_1 c_1) (p1 c_1 c_1) (not (p3 c_1)) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_1)) (not (p4 c_1)) (= c_1 c_1) (not (p14 c_1 c_1 c_1))) (or (not (p9 c_0)) (p3 (f12 c_0))) (or (not (p9 c_1)) (p3 (f12 c_1))) (or (not (p4 c_0)) (p1 (f6 c_0) c_0)) (or (not (p4 c_1)) (p1 (f6 c_1) c_1)) (or (not (p3 c_0)) (p4 (f2 c_0 c_0)) (= c_0 c_0) (not (p3 c_0))) (or (not (p3 c_0)) (p4 (f2 c_0 c_1)) (= c_0 c_1) (not (p3 c_1))) (or (not (p3 c_1)) (p4 (f2 c_1 c_0)) (= c_1 c_0) (not (p3 c_0))) (or (not (p3 c_1)) (p4 (f2 c_1 c_1)) (= c_1 c_1) (not (p3 c_1))) (or (not (p4 c_0)) (not (p3 c_0)) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_0)) (not (p1 c_0 c_0)) (not (p1 c_0 c_0)) (not (p4 c_0)) (not (p1 c_0 c_0))) (or (not (p4 c_0)) (not (p3 c_0)) (= c_0 c_0) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_1 c_0)) (not (p1 c_0 c_0)) (not (p1 c_1 c_0)) (not (p4 c_0)) (not (p1 c_0 c_0))) (or (not (p4 c_0)) (not (p3 c_0)) (= c_1 c_0) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_0)) (not (p1 c_0 c_1)) (not (p1 c_0 c_1)) (not (p4 c_1)) (not (p1 c_0 c_0))) (or (not (p4 c_0)) (not (p3 c_0)) (= c_1 c_0) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_1 c_0)) (not (p1 c_0 c_1)) (not (p1 c_1 c_1)) (not (p4 c_1)) (not (p1 c_0 c_0))) (or (not (p4 c_0)) (not (p3 c_1)) (= c_0 c_0) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_0 c_0)) (not (p1 c_1 c_0)) (not (p1 c_0 c_0)) (not (p4 c_0)) (not (p1 c_1 c_0))) (or (not (p4 c_0)) (not (p3 c_1)) (= c_0 c_0) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_0)) (not (p1 c_1 c_0)) (not (p1 c_1 c_0)) (not (p4 c_0)) (not (p1 c_1 c_0))) (or (not (p4 c_0)) (not (p3 c_1)) (= c_1 c_0) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_0 c_0)) (not (p1 c_1 c_1)) (not (p1 c_0 c_1)) (not (p4 c_1)) (not (p1 c_1 c_0))) (or (not (p4 c_0)) (not (p3 c_1)) (= c_1 c_0) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_0)) (not (p1 c_1 c_1)) (not (p1 c_1 c_1)) (not (p4 c_1)) (not (p1 c_1 c_0))) (or (not (p4 c_1)) (not (p3 c_0)) (= c_0 c_1) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_1)) (not (p1 c_0 c_0)) (not (p1 c_0 c_0)) (not (p4 c_0)) (not (p1 c_0 c_1))) (or (not (p4 c_1)) (not (p3 c_0)) (= c_0 c_1) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_1 c_1)) (not (p1 c_0 c_0)) (not (p1 c_1 c_0)) (not (p4 c_0)) (not (p1 c_0 c_1))) (or (not (p4 c_1)) (not (p3 c_0)) (= c_1 c_1) (not (p3 c_0)) (= c_0 c_0) (not (p1 c_0 c_1)) (not (p1 c_0 c_1)) (not (p1 c_0 c_1)) (not (p4 c_1)) (not (p1 c_0 c_1))) (or (not (p4 c_1)) (not (p3 c_0)) (= c_1 c_1) (not (p3 c_1)) (= c_0 c_1) (not (p1 c_1 c_1)) (not (p1 c_0 c_1)) (not (p1 c_1 c_1)) (not (p4 c_1)) (not (p1 c_0 c_1))) (or (not (p4 c_1)) (not (p3 c_1)) (= c_0 c_1) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_0 c_1)) (not (p1 c_1 c_0)) (not (p1 c_0 c_0)) (not (p4 c_0)) (not (p1 c_1 c_1))) (or (not (p4 c_1)) (not (p3 c_1)) (= c_0 c_1) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_1)) (not (p1 c_1 c_0)) (not (p1 c_1 c_0)) (not (p4 c_0)) (not (p1 c_1 c_1))) (or (not (p4 c_1)) (not (p3 c_1)) (= c_1 c_1) (not (p3 c_0)) (= c_1 c_0) (not (p1 c_0 c_1)) (not (p1 c_1 c_1)) (not (p1 c_0 c_1)) (not (p4 c_1)) (not (p1 c_1 c_1))) (or (not (p4 c_1)) (not (p3 c_1)) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1) (not (p1 c_1 c_1)) (not (p1 c_1 c_1)) (not (p1 c_1 c_1)) (not (p4 c_1)) (not (p1 c_1 c_1))) (or (= c_0 c_0) (not (p3 c_0)) (p1 c_0 (f2 c_0 c_0)) (not (p3 c_0))) (or (= c_0 c_1) (not (p3 c_1)) (p1 c_1 (f2 c_0 c_1)) (not (p3 c_0))) (or (= c_1 c_0) (not (p3 c_0)) (p1 c_0 (f2 c_1 c_0)) (not (p3 c_1))) (or (= c_1 c_1) (not (p3 c_1)) (p1 c_1 (f2 c_1 c_1)) (not (p3 c_1))) (or (= c_0 c_0) (not (p3 c_0)) (p4 (f17 c_0 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p14 c_0 c_0 c_0)) (not (p3 c_0)) (= c_0 c_0)) (or (= c_0 c_0) (not (p3 c_0)) (p4 (f17 c_0 c_1 c_0)) (= c_0 c_1) (not (p3 c_1)) (not (p14 c_0 c_1 c_0)) (not (p3 c_0)) (= c_1 c_0)) (or (= c_0 c_1) (not (p3 c_1)) (p4 (f17 c_0 c_0 c_1)) (= c_0 c_0) (not (p3 c_0)) (not (p14 c_0 c_0 c_1)) (not (p3 c_0)) (= c_0 c_1)) (or (= c_0 c_1) (not (p3 c_1)) (p4 (f17 c_0 c_1 c_1)) (= c_0 c_1) (not (p3 c_1)) (not (p14 c_0 c_1 c_1)) (not (p3 c_0)) (= c_1 c_1)) (or (= c_1 c_0) (not (p3 c_0)) (p4 (f17 c_1 c_0 c_0)) (= c_1 c_0) (not (p3 c_0)) (not (p14 c_1 c_0 c_0)) (not (p3 c_1)) (= c_0 c_0)) (or (= c_1 c_0) (not (p3 c_0)) (p4 (f17 c_1 c_1 c_0)) (= c_1 c_1) (not (p3 c_1)) (not (p14 c_1 c_1 c_0)) (not (p3 c_1)) (= c_1 c_0)) (or (= c_1 c_1) (not (p3 c_1)) (p4 (f17 c_1 c_0 c_1)) (= c_1 c_0) (not (p3 c_0)) (not (p14 c_1 c_0 c_1)) (not (p3 c_1)) (= c_0 c_1)) (or (= c_1 c_1) (not (p3 c_1)) (p4 (f17 c_1 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p14 c_1 c_1 c_1)) (not (p3 c_1)) (= c_1 c_1)) (or (= c_0 c_0) (= c_0 c_0) (= c_0 c_0) (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p1 c_0 c_0)) (not (p1 c_0 c_0)) (not (p3 c_0)) (not (p4 c_0)) (not (p3 c_0)) (not (p1 c_0 c_0))) (or (= c_0 c_0) (= c_0 c_0) (= c_0 c_0) (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p1 c_0 c_1)) (not (p1 c_0 c_1)) (not (p3 c_0)) (not (p4 c_1)) (not (p3 c_0)) (not (p1 c_0 c_1))) (or (= c_0 c_0) (= c_1 c_0) (= c_0 c_1) (p14 c_0 c_1 c_0) (not (p3 c_0)) (not (p1 c_1 c_0)) (not (p1 c_0 c_0)) (not (p3 c_0)) (not (p4 c_0)) (not (p3 c_1)) (not (p1 c_0 c_0))) (or (= c_0 c_0) (= c_1 c_0) (= c_0 c_1) (p14 c_0 c_1 c_0) (not (p3 c_0)) (not (p1 c_1 c_1)) (not (p1 c_0 c_1)) (not (p3 c_0)) (not (p4 c_1)) (not (p3 c_1)) (not (p1 c_0 c_1))) (or (= c_0 c_1) (= c_0 c_1) (= c_0 c_0) (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p1 c_0 c_0)) (not (p1 c_0 c_0)) (not (p3 c_1)) (not (p4 c_0)) (not (p3 c_0)) (not (p1 c_1 c_0))) (or (= c_0 c_1) (= c_0 c_1) (= c_0 c_0) (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p1 c_0 c_1)) (not (p1 c_0 c_1)) (not (p3 c_1)) (not (p4 c_1)) (not (p3 c_0)) (not (p1 c_1 c_1))) (or (= c_0 c_1) (= c_1 c_1) (= c_0 c_1) (p14 c_0 c_1 c_1) (not (p3 c_0)) (not (p1 c_1 c_0)) (not (p1 c_0 c_0)) (not (p3 c_1)) (not (p4 c_0)) (not (p3 c_1)) (not (p1 c_1 c_0))) (or (= c_0 c_1) (= c_1 c_1) (= c_0 c_1) (p14 c_0 c_1 c_1) (not (p3 c_0)) (not (p1 c_1 c_1)) (not (p1 c_0 c_1)) (not (p3 c_1)) (not (p4 c_1)) (not (p3 c_1)) (not (p1 c_1 c_1))) (or (= c_1 c_0) (= c_0 c_0) (= c_1 c_0) (p14 c_1 c_0 c_0) (not (p3 c_1)) (not (p1 c_0 c_0)) (not (p1 c_1 c_0)) (not (p3 c_0)) (not (p4 c_0)) (not (p3 c_0)) (not (p1 c_0 c_0))) (or (= c_1 c_0) (= c_0 c_0) (= c_1 c_0) (p14 c_1 c_0 c_0) (not (p3 c_1)) (not (p1 c_0 c_1)) (not (p1 c_1 c_1)) (not (p3 c_0)) (not (p4 c_1)) (not (p3 c_0)) (not (p1 c_0 c_1))) (or (= c_1 c_0) (= c_1 c_0) (= c_1 c_1) (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p1 c_1 c_0)) (not (p1 c_1 c_0)) (not (p3 c_0)) (not (p4 c_0)) (not (p3 c_1)) (not (p1 c_0 c_0))) (or (= c_1 c_0) (= c_1 c_0) (= c_1 c_1) (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p1 c_1 c_1)) (not (p1 c_1 c_1)) (not (p3 c_0)) (not (p4 c_1)) (not (p3 c_1)) (not (p1 c_0 c_1))) (or (= c_1 c_1) (= c_0 c_1) (= c_1 c_0) (p14 c_1 c_0 c_1) (not (p3 c_1)) (not (p1 c_0 c_0)) (not (p1 c_1 c_0)) (not (p3 c_1)) (not (p4 c_0)) (not (p3 c_0)) (not (p1 c_1 c_0))) (or (= c_1 c_1) (= c_0 c_1) (= c_1 c_0) (p14 c_1 c_0 c_1) (not (p3 c_1)) (not (p1 c_0 c_1)) (not (p1 c_1 c_1)) (not (p3 c_1)) (not (p4 c_1)) (not (p3 c_0)) (not (p1 c_1 c_1))) (or (= c_1 c_1) (= c_1 c_1) (= c_1 c_1) (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p1 c_1 c_0)) (not (p1 c_1 c_0)) (not (p3 c_1)) (not (p4 c_0)) (not (p3 c_1)) (not (p1 c_1 c_0))) (or (= c_1 c_1) (= c_1 c_1) (= c_1 c_1) (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p1 c_1 c_1)) (not (p1 c_1 c_1)) (not (p3 c_1)) (not (p4 c_1)) (not (p3 c_1)) (not (p1 c_1 c_1))) (or (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p3 c_0)) (p3 (f16 c_0 c_0 c_0)) (= c_0 c_0) (not (p9 c_0)) (not (p10 c_0 c_0))) (or (not (p9 c_0)) (not (p10 c_0 c_1)) (not (p3 c_0)) (p3 (f16 c_0 c_1 c_0)) (= c_0 c_1) (not (p9 c_1)) (not (p10 c_0 c_0))) (or (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p3 c_1)) (p3 (f16 c_0 c_0 c_1)) (= c_0 c_0) (not (p9 c_0)) (not (p10 c_1 c_0))) (or (not (p9 c_0)) (not (p10 c_1 c_1)) (not (p3 c_1)) (p3 (f16 c_0 c_1 c_1)) (= c_0 c_1) (not (p9 c_1)) (not (p10 c_1 c_0))) (or (not (p9 c_1)) (not (p10 c_0 c_0)) (not (p3 c_0)) (p3 (f16 c_1 c_0 c_0)) (= c_1 c_0) (not (p9 c_0)) (not (p10 c_0 c_1))) (or (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p3 c_0)) (p3 (f16 c_1 c_1 c_0)) (= c_1 c_1) (not (p9 c_1)) (not (p10 c_0 c_1))) (or (not (p9 c_1)) (not (p10 c_1 c_0)) (not (p3 c_1)) (p3 (f16 c_1 c_0 c_1)) (= c_1 c_0) (not (p9 c_0)) (not (p10 c_1 c_1))) (or (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p3 c_1)) (p3 (f16 c_1 c_1 c_1)) (= c_1 c_1) (not (p9 c_1)) (not (p10 c_1 c_1))) (or (not (p4 c_0)) (not (p1 (f7 c_0) c_0))) (or (not (p4 c_1)) (not (p1 (f7 c_1) c_1))) (or (not (p3 c_0)) (= c_0 c_0) (p10 c_0 (f13 c_0 c_0 c_0)) (not (p3 c_0)) (p14 c_0 c_0 c_0) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0)) (or (not (p3 c_0)) (= c_0 c_0) (p10 c_1 (f13 c_1 c_0 c_0)) (not (p3 c_1)) (p14 c_1 c_0 c_0) (= c_1 c_0) (not (p3 c_0)) (= c_1 c_0)) (or (not (p3 c_0)) (= c_1 c_0) (p10 c_0 (f13 c_0 c_1 c_0)) (not (p3 c_0)) (p14 c_0 c_1 c_0) (= c_0 c_1) (not (p3 c_1)) (= c_0 c_0)) (or (not (p3 c_0)) (= c_1 c_0) (p10 c_1 (f13 c_1 c_1 c_0)) (not (p3 c_1)) (p14 c_1 c_1 c_0) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_0)) (or (not (p3 c_1)) (= c_0 c_1) (p10 c_0 (f13 c_0 c_0 c_1)) (not (p3 c_0)) (p14 c_0 c_0 c_1) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_1)) (or (not (p3 c_1)) (= c_0 c_1) (p10 c_1 (f13 c_1 c_0 c_1)) (not (p3 c_1)) (p14 c_1 c_0 c_1) (= c_1 c_0) (not (p3 c_0)) (= c_1 c_1)) (or (not (p3 c_1)) (= c_1 c_1) (p10 c_0 (f13 c_0 c_1 c_1)) (not (p3 c_0)) (p14 c_0 c_1 c_1) (= c_0 c_1) (not (p3 c_1)) (= c_0 c_1)) (or (not (p3 c_1)) (= c_1 c_1) (p10 c_1 (f13 c_1 c_1 c_1)) (not (p3 c_1)) (p14 c_1 c_1 c_1) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1)) (p9 c18) (or (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_0) (p14 c_0 c_0 c_0) (not (p3 c_0)) (p10 c_0 (f13 c_0 c_0 c_0)) (not (p3 c_0))) (or (= c_0 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_0) (p14 c_1 c_0 c_0) (not (p3 c_0)) (p10 c_0 (f13 c_1 c_0 c_0)) (not (p3 c_0))) (or (= c_0 c_1) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_1) (p14 c_0 c_0 c_1) (not (p3 c_0)) (p10 c_1 (f13 c_0 c_0 c_1)) (not (p3 c_1))) (or (= c_0 c_1) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_1) (p14 c_1 c_0 c_1) (not (p3 c_0)) (p10 c_1 (f13 c_1 c_0 c_1)) (not (p3 c_1))) (or (= c_1 c_0) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_0) (p14 c_0 c_1 c_0) (not (p3 c_1)) (p10 c_0 (f13 c_0 c_1 c_0)) (not (p3 c_0))) (or (= c_1 c_0) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_0) (p14 c_1 c_1 c_0) (not (p3 c_1)) (p10 c_0 (f13 c_1 c_1 c_0)) (not (p3 c_0))) (or (= c_1 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_1) (p14 c_0 c_1 c_1) (not (p3 c_1)) (p10 c_1 (f13 c_0 c_1 c_1)) (not (p3 c_1))) (or (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_1) (p14 c_1 c_1 c_1) (not (p3 c_1)) (p10 c_1 (f13 c_1 c_1 c_1)) (not (p3 c_1))) (or (not (p3 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c18)) (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c18)) (not (p10 c_0 c18)) (= c_0 c_0) (= c_0 c_0)) (or (not (p3 c_0)) (= c_0 c_0) (not (p3 c_1)) (not (p10 c_1 c18)) (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p10 c_0 c18)) (not (p10 c_0 c18)) (= c_0 c_1) (= c_0 c_1)) (or (not (p3 c_0)) (= c_1 c_0) (not (p3 c_0)) (not (p10 c_0 c18)) (p14 c_1 c_0 c_0) (not (p3 c_1)) (not (p10 c_0 c18)) (not (p10 c_1 c18)) (= c_1 c_0) (= c_0 c_0)) (or (not (p3 c_0)) (= c_1 c_0) (not (p3 c_1)) (not (p10 c_1 c18)) (p14 c_1 c_0 c_1) (not (p3 c_1)) (not (p10 c_0 c18)) (not (p10 c_1 c18)) (= c_1 c_1) (= c_0 c_1)) (or (not (p3 c_1)) (= c_0 c_1) (not (p3 c_0)) (not (p10 c_0 c18)) (p14 c_0 c_1 c_0) (not (p3 c_0)) (not (p10 c_1 c18)) (not (p10 c_0 c18)) (= c_0 c_0) (= c_1 c_0)) (or (not (p3 c_1)) (= c_0 c_1) (not (p3 c_1)) (not (p10 c_1 c18)) (p14 c_0 c_1 c_1) (not (p3 c_0)) (not (p10 c_1 c18)) (not (p10 c_0 c18)) (= c_0 c_1) (= c_1 c_1)) (or (not (p3 c_1)) (= c_1 c_1) (not (p3 c_0)) (not (p10 c_0 c18)) (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p10 c_1 c18)) (not (p10 c_1 c18)) (= c_1 c_0) (= c_1 c_0)) (or (not (p3 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c18)) (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c18)) (not (p10 c_1 c18)) (= c_1 c_1) (= c_1 c_1)) (or (not (p9 c_0)) (p10 (f11 c_0) c_0)) (or (not (p9 c_1)) (p10 (f11 c_1) c_1)) (or (not (p4 c_0)) (p1 (f5 c_0) c_0)) (or (not (p4 c_1)) (p1 (f5 c_1) c_1)) (or (not (p10 c_0 c_0)) (not (p3 c_0)) (p10 (f16 c_0 c_0 c_0) c_0) (= c_0 c_0) (not (p10 c_0 c_0)) (not (p9 c_0)) (not (p9 c_0))) (or (not (p10 c_0 c_0)) (not (p3 c_0)) (p10 (f16 c_1 c_0 c_0) c_1) (= c_1 c_0) (not (p10 c_0 c_1)) (not (p9 c_1)) (not (p9 c_0))) (or (not (p10 c_0 c_1)) (not (p3 c_0)) (p10 (f16 c_0 c_1 c_0) c_0) (= c_0 c_1) (not (p10 c_0 c_0)) (not (p9 c_0)) (not (p9 c_1))) (or (not (p10 c_0 c_1)) (not (p3 c_0)) (p10 (f16 c_1 c_1 c_0) c_1) (= c_1 c_1) (not (p10 c_0 c_1)) (not (p9 c_1)) (not (p9 c_1))) (or (not (p10 c_1 c_0)) (not (p3 c_1)) (p10 (f16 c_0 c_0 c_1) c_0) (= c_0 c_0) (not (p10 c_1 c_0)) (not (p9 c_0)) (not (p9 c_0))) (or (not (p10 c_1 c_0)) (not (p3 c_1)) (p10 (f16 c_1 c_0 c_1) c_1) (= c_1 c_0) (not (p10 c_1 c_1)) (not (p9 c_1)) (not (p9 c_0))) (or (not (p10 c_1 c_1)) (not (p3 c_1)) (p10 (f16 c_0 c_1 c_1) c_0) (= c_0 c_1) (not (p10 c_1 c_0)) (not (p9 c_0)) (not (p9 c_1))) (or (not (p10 c_1 c_1)) (not (p3 c_1)) (p10 (f16 c_1 c_1 c_1) c_1) (= c_1 c_1) (not (p10 c_1 c_1)) (not (p9 c_1)) (not (p9 c_1))) (or (not (p4 c_0)) (not (= (f5 c_0) (f6 c_0)))) (or (not (p4 c_1)) (not (= (f5 c_1) (f6 c_1)))) (or (not (p4 c_0)) (p3 (f5 c_0))) (or (not (p4 c_1)) (p3 (f5 c_1))) (or (= c_0 c_0) (not (p3 c_0)) (p1 c_0 (f17 c_0 c_0 c_0)) (not (p3 c_0)) (not (p14 c_0 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0)) (or (= c_0 c_0) (not (p3 c_0)) (p1 c_0 (f17 c_1 c_0 c_0)) (not (p3 c_0)) (not (p14 c_1 c_0 c_0)) (= c_1 c_0) (not (p3 c_1)) (= c_1 c_0)) (or (= c_0 c_1) (not (p3 c_0)) (p1 c_0 (f17 c_0 c_0 c_1)) (not (p3 c_1)) (not (p14 c_0 c_0 c_1)) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_1)) (or (= c_0 c_1) (not (p3 c_0)) (p1 c_0 (f17 c_1 c_0 c_1)) (not (p3 c_1)) (not (p14 c_1 c_0 c_1)) (= c_1 c_0) (not (p3 c_1)) (= c_1 c_1)) (or (= c_1 c_0) (not (p3 c_1)) (p1 c_1 (f17 c_0 c_1 c_0)) (not (p3 c_0)) (not (p14 c_0 c_1 c_0)) (= c_0 c_1) (not (p3 c_0)) (= c_0 c_0)) (or (= c_1 c_0) (not (p3 c_1)) (p1 c_1 (f17 c_1 c_1 c_0)) (not (p3 c_0)) (not (p14 c_1 c_1 c_0)) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_0)) (or (= c_1 c_1) (not (p3 c_1)) (p1 c_1 (f17 c_0 c_1 c_1)) (not (p3 c_1)) (not (p14 c_0 c_1 c_1)) (= c_0 c_1) (not (p3 c_0)) (= c_0 c_1)) (or (= c_1 c_1) (not (p3 c_1)) (p1 c_1 (f17 c_1 c_1 c_1)) (not (p3 c_1)) (not (p14 c_1 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1)) (or (not (p3 c_0)) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_0) (p9 (f13 c_0 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (p14 c_0 c_0 c_0)) (or (not (p3 c_0)) (not (p3 c_0)) (= c_1 c_0) (= c_0 c_0) (p9 (f13 c_0 c_1 c_0)) (= c_0 c_1) (not (p3 c_1)) (p14 c_0 c_1 c_0)) (or (not (p3 c_0)) (not (p3 c_1)) (= c_0 c_1) (= c_0 c_1) (p9 (f13 c_0 c_0 c_1)) (= c_0 c_0) (not (p3 c_0)) (p14 c_0 c_0 c_1)) (or (not (p3 c_0)) (not (p3 c_1)) (= c_1 c_1) (= c_0 c_1) (p9 (f13 c_0 c_1 c_1)) (= c_0 c_1) (not (p3 c_1)) (p14 c_0 c_1 c_1)) (or (not (p3 c_1)) (not (p3 c_0)) (= c_0 c_0) (= c_1 c_0) (p9 (f13 c_1 c_0 c_0)) (= c_1 c_0) (not (p3 c_0)) (p14 c_1 c_0 c_0)) (or (not (p3 c_1)) (not (p3 c_0)) (= c_1 c_0) (= c_1 c_0) (p9 (f13 c_1 c_1 c_0)) (= c_1 c_1) (not (p3 c_1)) (p14 c_1 c_1 c_0)) (or (not (p3 c_1)) (not (p3 c_1)) (= c_0 c_1) (= c_1 c_1) (p9 (f13 c_1 c_0 c_1)) (= c_1 c_0) (not (p3 c_0)) (p14 c_1 c_0 c_1)) (or (not (p3 c_1)) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_1) (p9 (f13 c_1 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (p14 c_1 c_1 c_1)) (or (p1 c_0 (f17 c_0 c_0 c_0)) (not (p14 c_0 c_0 c_0)) (not (p3 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_0)) (or (p1 c_0 (f17 c_0 c_1 c_0)) (not (p14 c_0 c_1 c_0)) (not (p3 c_0)) (= c_0 c_1) (not (p3 c_1)) (not (p3 c_0)) (= c_1 c_0) (= c_0 c_0)) (or (p1 c_0 (f17 c_1 c_0 c_0)) (not (p14 c_1 c_0 c_0)) (not (p3 c_1)) (= c_1 c_0) (not (p3 c_0)) (not (p3 c_0)) (= c_0 c_0) (= c_1 c_0)) (or (p1 c_0 (f17 c_1 c_1 c_0)) (not (p14 c_1 c_1 c_0)) (not (p3 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p3 c_0)) (= c_1 c_0) (= c_1 c_0)) (or (p1 c_1 (f17 c_0 c_0 c_1)) (not (p14 c_0 c_0 c_1)) (not (p3 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p3 c_1)) (= c_0 c_1) (= c_0 c_1)) (or (p1 c_1 (f17 c_0 c_1 c_1)) (not (p14 c_0 c_1 c_1)) (not (p3 c_0)) (= c_0 c_1) (not (p3 c_1)) (not (p3 c_1)) (= c_1 c_1) (= c_0 c_1)) (or (p1 c_1 (f17 c_1 c_0 c_1)) (not (p14 c_1 c_0 c_1)) (not (p3 c_1)) (= c_1 c_0) (not (p3 c_0)) (not (p3 c_1)) (= c_0 c_1) (= c_1 c_1)) (or (p1 c_1 (f17 c_1 c_1 c_1)) (not (p14 c_1 c_1 c_1)) (not (p3 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_1)) (or (not (p10 c_0 c_0)) (= c_0 c_0) (not (p9 c_0)) (not (p9 c_0)) (p10 (f16 c_0 c_0 c_0) c_0) (not (p10 c_0 c_0)) (not (p3 c_0))) (or (not (p10 c_0 c_0)) (= c_1 c_0) (not (p9 c_0)) (not (p9 c_1)) (p10 (f16 c_1 c_0 c_0) c_0) (not (p10 c_0 c_1)) (not (p3 c_0))) (or (not (p10 c_0 c_1)) (= c_0 c_1) (not (p9 c_1)) (not (p9 c_0)) (p10 (f16 c_0 c_1 c_0) c_1) (not (p10 c_0 c_0)) (not (p3 c_0))) (or (not (p10 c_0 c_1)) (= c_1 c_1) (not (p9 c_1)) (not (p9 c_1)) (p10 (f16 c_1 c_1 c_0) c_1) (not (p10 c_0 c_1)) (not (p3 c_0))) (or (not (p10 c_1 c_0)) (= c_0 c_0) (not (p9 c_0)) (not (p9 c_0)) (p10 (f16 c_0 c_0 c_1) c_0) (not (p10 c_1 c_0)) (not (p3 c_1))) (or (not (p10 c_1 c_0)) (= c_1 c_0) (not (p9 c_0)) (not (p9 c_1)) (p10 (f16 c_1 c_0 c_1) c_0) (not (p10 c_1 c_1)) (not (p3 c_1))) (or (not (p10 c_1 c_1)) (= c_0 c_1) (not (p9 c_1)) (not (p9 c_0)) (p10 (f16 c_0 c_1 c_1) c_1) (not (p10 c_1 c_0)) (not (p3 c_1))) (or (not (p10 c_1 c_1)) (= c_1 c_1) (not (p9 c_1)) (not (p9 c_1)) (p10 (f16 c_1 c_1 c_1) c_1) (not (p10 c_1 c_1)) (not (p3 c_1))) (p4 c8) (or (not (p3 c_0)) (= c_0 c_0) (p1 c_0 (f2 c_0 c_0)) (not (p3 c_0))) (or (not (p3 c_0)) (= c_1 c_0) (p1 c_1 (f2 c_1 c_0)) (not (p3 c_1))) (or (not (p3 c_1)) (= c_0 c_1) (p1 c_0 (f2 c_0 c_1)) (not (p3 c_0))) (or (not (p3 c_1)) (= c_1 c_1) (p1 c_1 (f2 c_1 c_1)) (not (p3 c_1))) (or (= c_0 c_0) (= c_0 c_0) (not (p3 c_0)) (p1 c_0 (f17 c_0 c_0 c_0)) (not (p14 c_0 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p3 c_0))) (or (= c_0 c_0) (= c_1 c_0) (not (p3 c_0)) (p1 c_1 (f17 c_1 c_0 c_0)) (not (p14 c_1 c_0 c_0)) (= c_1 c_0) (not (p3 c_0)) (not (p3 c_1))) (or (= c_0 c_1) (= c_0 c_1) (not (p3 c_0)) (p1 c_0 (f17 c_0 c_0 c_1)) (not (p14 c_0 c_0 c_1)) (= c_0 c_0) (not (p3 c_1)) (not (p3 c_0))) (or (= c_0 c_1) (= c_1 c_1) (not (p3 c_0)) (p1 c_1 (f17 c_1 c_0 c_1)) (not (p14 c_1 c_0 c_1)) (= c_1 c_0) (not (p3 c_1)) (not (p3 c_1))) (or (= c_1 c_0) (= c_0 c_0) (not (p3 c_1)) (p1 c_0 (f17 c_0 c_1 c_0)) (not (p14 c_0 c_1 c_0)) (= c_0 c_1) (not (p3 c_0)) (not (p3 c_0))) (or (= c_1 c_0) (= c_1 c_0) (not (p3 c_1)) (p1 c_1 (f17 c_1 c_1 c_0)) (not (p14 c_1 c_1 c_0)) (= c_1 c_1) (not (p3 c_0)) (not (p3 c_1))) (or (= c_1 c_1) (= c_0 c_1) (not (p3 c_1)) (p1 c_0 (f17 c_0 c_1 c_1)) (not (p14 c_0 c_1 c_1)) (= c_0 c_1) (not (p3 c_1)) (not (p3 c_0))) (or (= c_1 c_1) (= c_1 c_1) (not (p3 c_1)) (p1 c_1 (f17 c_1 c_1 c_1)) (not (p14 c_1 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p3 c_1))) (or (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_0)) (not (p10 c_0 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_0) (not (p10 c_0 c_0))) (or (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_0)) (not (p10 c_0 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_0) (not (p10 c_0 c_0))) (or (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_1)) (not (p10 c_0 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_0 c_0)) (= c_1 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_0) (not (p10 c_0 c_1))) (or (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_1)) (not (p10 c_0 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_0 c_1)) (= c_1 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_0) (not (p10 c_0 c_1))) (or (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_0)) (not (p10 c_0 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_1 c_0)) (= c_0 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_0) (not (p10 c_0 c_0))) (or (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_0)) (not (p10 c_0 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_1 c_1)) (= c_0 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_0) (not (p10 c_0 c_0))) (or (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_1)) (not (p10 c_0 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_0) (not (p10 c_0 c_1))) (or (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_1)) (not (p10 c_0 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_0) (not (p10 c_0 c_1))) (or (p14 c_0 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_0)) (not (p10 c_0 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_1) (not (p10 c_1 c_0))) (or (p14 c_0 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_0)) (not (p10 c_0 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_1) (not (p10 c_1 c_0))) (or (p14 c_0 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_1)) (not (p10 c_0 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_0 c_0)) (= c_1 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_1) (not (p10 c_1 c_1))) (or (p14 c_0 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_1)) (not (p10 c_0 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_0 c_1)) (= c_1 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_0) (not (p3 c_0)) (= c_0 c_0) (= c_0 c_1) (not (p10 c_1 c_1))) (or (p14 c_0 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_0)) (not (p10 c_0 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_1 c_0)) (= c_0 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_1) (not (p10 c_1 c_0))) (or (p14 c_0 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_0)) (not (p10 c_0 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (not (p10 c_1 c_1)) (= c_0 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_1) (not (p10 c_1 c_0))) (or (p14 c_0 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_1)) (not (p10 c_0 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_1) (not (p10 c_1 c_1))) (or (p14 c_0 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_1)) (not (p10 c_0 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_0)) (= c_0 c_1) (= c_0 c_1) (not (p10 c_1 c_1))) (or (p14 c_1 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_0)) (not (p10 c_1 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_0) (not (p10 c_0 c_0))) (or (p14 c_1 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_0)) (not (p10 c_1 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_0) (not (p10 c_0 c_0))) (or (p14 c_1 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_1)) (not (p10 c_1 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_0 c_0)) (= c_1 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_0) (not (p10 c_0 c_1))) (or (p14 c_1 c_0 c_0) (not (p3 c_0)) (not (p10 c_0 c_1)) (not (p10 c_1 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_0 c_1)) (= c_1 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_0) (not (p10 c_0 c_1))) (or (p14 c_1 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_0)) (not (p10 c_1 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_1 c_0)) (= c_0 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_0) (not (p10 c_0 c_0))) (or (p14 c_1 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_0)) (not (p10 c_1 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_1 c_1)) (= c_0 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_0) (not (p10 c_0 c_0))) (or (p14 c_1 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_1)) (not (p10 c_1 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_0 c_0)) (= c_0 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_0) (not (p10 c_0 c_1))) (or (p14 c_1 c_0 c_1) (not (p3 c_0)) (not (p10 c_1 c_1)) (not (p10 c_1 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_0) (not (p10 c_0 c_1))) (or (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_0)) (not (p10 c_1 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_0 c_0)) (= c_0 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_1) (not (p10 c_1 c_0))) (or (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_0)) (not (p10 c_1 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_0 c_1)) (= c_0 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_1) (not (p10 c_1 c_0))) (or (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_1)) (not (p10 c_1 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_0 c_0)) (= c_1 c_0) (not (p3 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_1) (not (p10 c_1 c_1))) (or (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p10 c_0 c_1)) (not (p10 c_1 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_0 c_1)) (= c_1 c_1) (not (p3 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_0) (not (p3 c_1)) (= c_1 c_0) (= c_1 c_1) (not (p10 c_1 c_1))) (or (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_0)) (not (p10 c_1 c_0)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_1 c_0)) (= c_0 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_1) (not (p10 c_1 c_0))) (or (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_0)) (not (p10 c_1 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (not (p10 c_1 c_1)) (= c_0 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_1) (not (p10 c_1 c_0))) (or (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_1)) (not (p10 c_1 c_0)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_1 c_0)) (= c_1 c_0) (not (p3 c_1)) (not (p9 c_0)) (not (p10 c_1 c_0)) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_1) (not (p10 c_1 c_1))) (or (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p10 c_1 c_1)) (not (p10 c_1 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (not (p9 c_1)) (not (p10 c_1 c_1)) (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1) (= c_1 c_1) (not (p10 c_1 c_1))) (or (= c_0 c_0) (not (p3 c_0)) (= c_0 c_0) (p14 c_0 c_0 c_0) (not (p3 c_0)) (not (p3 c_0)) (= c_0 c_0) (p10 c_0 (f13 c_0 c_0 c_0))) (or (= c_0 c_0) (not (p3 c_0)) (= c_0 c_1) (p14 c_0 c_0 c_1) (not (p3 c_0)) (not (p3 c_1)) (= c_0 c_1) (p10 c_0 (f13 c_0 c_0 c_1))) (or (= c_0 c_1) (not (p3 c_0)) (= c_1 c_0) (p14 c_0 c_1 c_0) (not (p3 c_1)) (not (p3 c_0)) (= c_0 c_0) (p10 c_1 (f13 c_0 c_1 c_0))) (or (= c_0 c_1) (not (p3 c_0)) (= c_1 c_1) (p14 c_0 c_1 c_1) (not (p3 c_1)) (not (p3 c_1)) (= c_0 c_1) (p10 c_1 (f13 c_0 c_1 c_1))) (or (= c_1 c_0) (not (p3 c_1)) (= c_0 c_0) (p14 c_1 c_0 c_0) (not (p3 c_0)) (not (p3 c_0)) (= c_1 c_0) (p10 c_0 (f13 c_1 c_0 c_0))) (or (= c_1 c_0) (not (p3 c_1)) (= c_0 c_1) (p14 c_1 c_0 c_1) (not (p3 c_0)) (not (p3 c_1)) (= c_1 c_1) (p10 c_0 (f13 c_1 c_0 c_1))) (or (= c_1 c_1) (not (p3 c_1)) (= c_1 c_0) (p14 c_1 c_1 c_0) (not (p3 c_1)) (not (p3 c_0)) (= c_1 c_0) (p10 c_1 (f13 c_1 c_1 c_0))) (or (= c_1 c_1) (not (p3 c_1)) (= c_1 c_1) (p14 c_1 c_1 c_1) (not (p3 c_1)) (not (p3 c_1)) (= c_1 c_1) (p10 c_1 (f13 c_1 c_1 c_1))) (or (p3 (f7 c_0)) (not (p4 c_0))) (or (p3 (f7 c_1)) (not (p4 c_1))) (or (not (= c_0 (f16 c_0 c_0 c_0))) (not (p10 c_0 c_0)) (not (p10 c_0 c_0)) (not (p9 c_0)) (not (p3 c_0)) (= c_0 c_0) (not (p9 c_0))) (or (not (= c_0 (f16 c_0 c_1 c_0))) (not (p10 c_0 c_0)) (not (p10 c_0 c_1)) (not (p9 c_0)) (not (p3 c_0)) (= c_0 c_1) (not (p9 c_1))) (or (not (= c_0 (f16 c_1 c_0 c_0))) (not (p10 c_0 c_1)) (not (p10 c_0 c_0)) (not (p9 c_1)) (not (p3 c_0)) (= c_1 c_0) (not (p9 c_0))) (or (not (= c_0 (f16 c_1 c_1 c_0))) (not (p10 c_0 c_1)) (not (p10 c_0 c_1)) (not (p9 c_1)) (not (p3 c_0)) (= c_1 c_1) (not (p9 c_1))) (or (not (= c_1 (f16 c_0 c_0 c_1))) (not (p10 c_1 c_0)) (not (p10 c_1 c_0)) (not (p9 c_0)) (not (p3 c_1)) (= c_0 c_0) (not (p9 c_0))) (or (not (= c_1 (f16 c_0 c_1 c_1))) (not (p10 c_1 c_0)) (not (p10 c_1 c_1)) (not (p9 c_0)) (not (p3 c_1)) (= c_0 c_1) (not (p9 c_1))) (or (not (= c_1 (f16 c_1 c_0 c_1))) (not (p10 c_1 c_1)) (not (p10 c_1 c_0)) (not (p9 c_1)) (not (p3 c_1)) (= c_1 c_0) (not (p9 c_0))) (or (not (= c_1 (f16 c_1 c_1 c_1))) (not (p10 c_1 c_1)) (not (p10 c_1 c_1)) (not (p9 c_1)) (not (p3 c_1)) (= c_1 c_1) (not (p9 c_1))) (or (p3 (f6 c_0)) (not (p4 c_0))) (or (p3 (f6 c_1)) (not (p4 c_1))) (or (not (p9 c_0)) (not (p1 c_0 c_0)) (= c_0 c_0) (not (p10 c_0 c_0)) (p15 c_0 c_0) (not (p10 c_0 c_0)) (not (p3 c_0)) (not (p4 c_0)) (not (p1 c_0 c_0)) (not (p3 c_0))) (or (not (p9 c_0)) (not (p1 c_0 c_0)) (= c_1 c_0) (not (p10 c_0 c_0)) (p15 c_0 c_0) (not (p10 c_1 c_0)) (not (p3 c_0)) (not (p4 c_0)) (not (p1 c_1 c_0)) (not (p3 c_1))) (or (not (p9 c_0)) (not (p1 c_0 c_1)) (= c_0 c_0) (not (p10 c_0 c_0)) (p15 c_1 c_0) (not (p10 c_0 c_0)) (not (p3 c_0)) (not (p4 c_1)) (not (p1 c_0 c_1)) (not (p3 c_0))) (or (not (p9 c_0)) (not (p1 c_0 c_1)) (= c_1 c_0) (not (p10 c_0 c_0)) (p15 c_1 c_0) (not (p10 c_1 c_0)) (not (p3 c_0)) (not (p4 c_1)) (not (p1 c_1 c_1)) (not (p3 c_1))) (or (not (p9 c_0)) (not (p1 c_1 c_0)) (= c_0 c_1) (not (p10 c_1 c_0)) (p15 c_0 c_0) (not (p10 c_0 c_0)) (not (p3 c_1)) (not (p4 c_0)) (not (p1 c_0 c_0)) (not (p3 c_0))) (or (not (p9 c_0)) (not (p1 c_1 c_0)) (= c_1 c_1) (not (p10 c_1 c_0)) (p15 c_0 c_0) (not (p10 c_1 c_0)) (not (p3 c_1)) (not (p4 c_0)) (not (p1 c_1 c_0)) (not (p3 c_1))) (or (not (p9 c_0)) (not (p1 c_1 c_1)) (= c_0 c_1) (not (p10 c_1 c_0)) (p15 c_1 c_0) (not (p10 c_0 c_0)) (not (p3 c_1)) (not (p4 c_1)) (not (p1 c_0 c_1)) (not (p3 c_0))) (or (not (p9 c_0)) (not (p1 c_1 c_1)) (= c_1 c_1) (not (p10 c_1 c_0)) (p15 c_1 c_0) (not (p10 c_1 c_0)) (not (p3 c_1)) (not (p4 c_1)) (not (p1 c_1 c_1)) (not (p3 c_1))) (or (not (p9 c_1)) (not (p1 c_0 c_0)) (= c_0 c_0) (not (p10 c_0 c_1)) (p15 c_0 c_1) (not (p10 c_0 c_1)) (not (p3 c_0)) (not (p4 c_0)) (not (p1 c_0 c_0)) (not (p3 c_0))) (or (not (p9 c_1)) (not (p1 c_0 c_0)) (= c_1 c_0) (not (p10 c_0 c_1)) (p15 c_0 c_1) (not (p10 c_1 c_1)) (not (p3 c_0)) (not (p4 c_0)) (not (p1 c_1 c_0)) (not (p3 c_1))) (or (not (p9 c_1)) (not (p1 c_0 c_1)) (= c_0 c_0) (not (p10 c_0 c_1)) (p15 c_1 c_1) (not (p10 c_0 c_1)) (not (p3 c_0)) (not (p4 c_1)) (not (p1 c_0 c_1)) (not (p3 c_0))) (or (not (p9 c_1)) (not (p1 c_0 c_1)) (= c_1 c_0) (not (p10 c_0 c_1)) (p15 c_1 c_1) (not (p10 c_1 c_1)) (not (p3 c_0)) (not (p4 c_1)) (not (p1 c_1 c_1)) (not (p3 c_1))) (or (not (p9 c_1)) (not (p1 c_1 c_0)) (= c_0 c_1) (not (p10 c_1 c_1)) (p15 c_0 c_1) (not (p10 c_0 c_1)) (not (p3 c_1)) (not (p4 c_0)) (not (p1 c_0 c_0)) (not (p3 c_0))) (or (not (p9 c_1)) (not (p1 c_1 c_0)) (= c_1 c_1) (not (p10 c_1 c_1)) (p15 c_0 c_1) (not (p10 c_1 c_1)) (not (p3 c_1)) (not (p4 c_0)) (not (p1 c_1 c_0)) (not (p3 c_1))) (or (not (p9 c_1)) (not (p1 c_1 c_1)) (= c_0 c_1) (not (p10 c_1 c_1)) (p15 c_1 c_1) (not (p10 c_0 c_1)) (not (p3 c_1)) (not (p4 c_1)) (not (p1 c_0 c_1)) (not (p3 c_0))) (or (not (p9 c_1)) (not (p1 c_1 c_1)) (= c_1 c_1) (not (p10 c_1 c_1)) (p15 c_1 c_1) (not (p10 c_1 c_1)) (not (p3 c_1)) (not (p4 c_1)) (not (p1 c_1 c_1)) (not (p3 c_1))) (or (not (p9 c_0)) (p3 (f11 c_0))) (or (not (p9 c_1)) (p3 (f11 c_1))) (or (not (p9 c_0)) (not (p10 (f12 c_0) c_0))) (or (not (p9 c_1)) (not (p10 (f12 c_1) c_1))) (or (= (f17 c_0 c_0 c_0) c_0) (= (f17 c_0 c_0 c_0) c_1)) (or (= (f17 c_0 c_0 c_1) c_0) (= (f17 c_0 c_0 c_1) c_1)) (or (= (f17 c_0 c_1 c_0) c_0) (= (f17 c_0 c_1 c_0) c_1)) (or (= (f17 c_0 c_1 c_1) c_0) (= (f17 c_0 c_1 c_1) c_1)) (or (= (f17 c_1 c_0 c_0) c_0) (= (f17 c_1 c_0 c_0) c_1)) (or (= (f17 c_1 c_0 c_1) c_0) (= (f17 c_1 c_0 c_1) c_1)) (or (= (f17 c_1 c_1 c_0) c_0) (= (f17 c_1 c_1 c_0) c_1)) (or (= (f17 c_1 c_1 c_1) c_0) (= (f17 c_1 c_1 c_1) c_1)) (or (= (f16 c_0 c_0 c_0) c_0) (= (f16 c_0 c_0 c_0) c_1)) (or (= (f16 c_0 c_0 c_1) c_0) (= (f16 c_0 c_0 c_1) c_1)) (or (= (f16 c_0 c_1 c_0) c_0) (= (f16 c_0 c_1 c_0) c_1)) (or (= (f16 c_0 c_1 c_1) c_0) (= (f16 c_0 c_1 c_1) c_1)) (or (= (f16 c_1 c_0 c_0) c_0) (= (f16 c_1 c_0 c_0) c_1)) (or (= (f16 c_1 c_0 c_1) c_0) (= (f16 c_1 c_0 c_1) c_1)) (or (= (f16 c_1 c_1 c_0) c_0) (= (f16 c_1 c_1 c_0) c_1)) (or (= (f16 c_1 c_1 c_1) c_0) (= (f16 c_1 c_1 c_1) c_1)) (or (= (f13 c_0 c_0 c_0) c_0) (= (f13 c_0 c_0 c_0) c_1)) (or (= (f13 c_0 c_0 c_1) c_0) (= (f13 c_0 c_0 c_1) c_1)) (or (= (f13 c_0 c_1 c_0) c_0) (= (f13 c_0 c_1 c_0) c_1)) (or (= (f13 c_0 c_1 c_1) c_0) (= (f13 c_0 c_1 c_1) c_1)) (or (= (f13 c_1 c_0 c_0) c_0) (= (f13 c_1 c_0 c_0) c_1)) (or (= (f13 c_1 c_0 c_1) c_0) (= (f13 c_1 c_0 c_1) c_1)) (or (= (f13 c_1 c_1 c_0) c_0) (= (f13 c_1 c_1 c_0) c_1)) (or (= (f13 c_1 c_1 c_1) c_0) (= (f13 c_1 c_1 c_1) c_1)) (or (= (f2 c_0 c_0) c_0) (= (f2 c_0 c_0) c_1)) (or (= (f2 c_0 c_1) c_0) (= (f2 c_0 c_1) c_1)) (or (= (f2 c_1 c_0) c_0) (= (f2 c_1 c_0) c_1)) (or (= (f2 c_1 c_1) c_0) (= (f2 c_1 c_1) c_1)) (or (= (f12 c_0) c_0) (= (f12 c_0) c_1)) (or (= (f12 c_1) c_0) (= (f12 c_1) c_1)) (or (= (f6 c_0) c_0) (= (f6 c_0) c_1)) (or (= (f6 c_1) c_0) (= (f6 c_1) c_1)) (or (= (f7 c_0) c_0) (= (f7 c_0) c_1)) (or (= (f7 c_1) c_0) (= (f7 c_1) c_1)) (or (= (f11 c_0) c_0) (= (f11 c_0) c_1)) (or (= (f11 c_1) c_0) (= (f11 c_1) c_1)) (or (= (f5 c_0) c_0) (= (f5 c_0) c_1)) (or (= (f5 c_1) c_0) (= (f5 c_1) c_1)) (or (= c18 c_0) (= c18 c_1)) (or (= c8 c_0) (= c8 c_1))))
(assert (not (or (= c8 c_0) (= c8 c_1))))
(check-sat)
(exit)
