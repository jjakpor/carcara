(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (not (or (or (not car) (not clk)) (not (not car)))))
(assert (not (not (or (not car) (not clk)))))
(check-sat)
(exit)
