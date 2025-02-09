(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (or (or (or (not car) (not clk)) (not (not car))) (or (or (not car) (not clk)) (not (not car)))))
(assert (not (or (or (not car) (not clk)) (not (not car)))))
(check-sat)
(exit)
