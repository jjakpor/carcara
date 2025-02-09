(set-logic QF_UF)
(declare-sort Z 0)
(declare-fun circuit () Bool)
(declare-fun input () Bool)
(declare-fun reg () Bool)
(declare-fun flash () Z)
(declare-fun nf () Z)
(declare-fun nf0 () Z)
(assert (or (not (= (= flash nf) (= flash nf0))) (not (= flash nf)) (= flash nf0)))
(assert (= (= flash nf) (= flash nf0)))
(assert (= flash nf))
(assert (not (= flash nf0)))
(check-sat)
(exit)
