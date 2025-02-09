(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (or prt (not (or (not car) (not clk)))))
(assert (not prt))
(assert (not (not (or (not car) (not clk)))))
(check-sat)
(exit)
