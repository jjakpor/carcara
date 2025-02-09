(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (not (not (= (or (or (not car) (not clk)) (not (not clk))) (or (or (not car) (not clk)) clk)))))
(assert (not (not (or (or (not car) (not clk)) (not (not clk))))))
(assert (not (or (or (not car) (not clk)) clk)))
(check-sat)
(exit)
