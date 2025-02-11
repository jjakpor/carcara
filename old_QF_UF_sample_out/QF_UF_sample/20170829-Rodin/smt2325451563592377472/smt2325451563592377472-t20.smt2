(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (or (or (not prt) (not car) (not (not clk))) (or (not prt) (not car) (not (not clk))) (or (not prt) (not car) (not (not clk)))))
(assert (not (or (not prt) (not car) (not (not clk)))))
(check-sat)
(exit)
