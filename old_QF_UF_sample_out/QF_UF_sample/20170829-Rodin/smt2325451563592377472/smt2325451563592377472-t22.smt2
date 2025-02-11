(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (or (not prt) (not car) clk))
(assert (not (not prt)))
(assert (not (not car)))
(assert (not clk))
(check-sat)
(exit)
