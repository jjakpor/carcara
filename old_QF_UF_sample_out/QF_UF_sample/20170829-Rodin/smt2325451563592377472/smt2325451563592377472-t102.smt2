(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (or (not (= (or (or (not car) clk) (not (not car))) (or (or (not car) clk) car))) (not (or (or (not car) clk) (not (not car)))) (or (or (not car) clk) car)))
(assert (= (or (or (not car) clk) (not (not car))) (or (or (not car) clk) car)))
(assert (or (or (not car) clk) (not (not car))))
(assert (not (or (or (not car) clk) car)))
(check-sat)
(exit)
