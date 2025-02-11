(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (or (or (not car) (not clk)) car))
(assert (not (or (not car) (not clk))))
(assert (not car))
(check-sat)
(exit)
