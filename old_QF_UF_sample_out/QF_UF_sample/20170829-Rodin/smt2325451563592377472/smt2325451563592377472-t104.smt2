(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (or (or (not car) clk) car))
(assert (not car))
(assert (not (or (not car) clk)))
(check-sat)
(exit)
