(set-logic QF_UF)
(declare-sort Z 0)
(declare-fun circuit () Bool)
(declare-fun input () Bool)
(declare-fun reg () Bool)
(declare-fun flash () Z)
(declare-fun nf () Z)
(declare-fun nf0 () Z)
(assert (= (not (= nf0 nf0)) false))
(assert (= (= nf0 nf0) true))
(assert (not (= (and (not (= nf0 nf0)) (= nf0 nf0)) (and false true))))
(check-sat)
(exit)
