(set-logic QF_UF)
(declare-sort Z 0)
(declare-fun circuit () Bool)
(declare-fun input () Bool)
(declare-fun reg () Bool)
(declare-fun flash () Z)
(declare-fun nf () Z)
(declare-fun nf0 () Z)
(assert (or (not (not (not (= nf nf0)))) (= nf nf0)))
(assert (not (not (= nf nf0))))
(assert (not (= nf nf0)))
(check-sat)
(exit)
