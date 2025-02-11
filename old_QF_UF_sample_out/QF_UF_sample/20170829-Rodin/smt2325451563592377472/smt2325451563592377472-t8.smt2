(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (= clk clk))
(assert (= (not (not clk)) clk))
(assert (not (= (= clk (not (not clk))) (= clk clk))))
(check-sat)
(exit)
