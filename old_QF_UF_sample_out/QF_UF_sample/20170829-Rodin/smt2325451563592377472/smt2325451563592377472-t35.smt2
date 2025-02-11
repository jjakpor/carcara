(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (= (= prt (not (not prt))) (= prt prt)))
(assert (= (= prt prt) true))
(assert (not (= (= prt (not (not prt))) true)))
(check-sat)
(exit)
