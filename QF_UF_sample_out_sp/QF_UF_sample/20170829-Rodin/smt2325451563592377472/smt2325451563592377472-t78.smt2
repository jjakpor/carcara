(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (not (or (not car) (not clk))))
(assert (not car))
(assert (or (or (not car) (not clk)) car))
(check-sat)
(exit)
