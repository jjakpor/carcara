(set-logic QF_UF)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-sort S5 0)
(declare-sort S6 0)
(declare-sort S7 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3 S4 S5 S6) S1)
(declare-fun f4 () S2)
(declare-fun f5 () S3)
(declare-fun f6 () S4)
(declare-fun f7 () S5)
(declare-fun f8 (S7) S6)
(declare-fun f9 () S7)
(declare-fun f10 () S6)
(assert (not (= f5 f5)))
(check-sat)
(exit)
