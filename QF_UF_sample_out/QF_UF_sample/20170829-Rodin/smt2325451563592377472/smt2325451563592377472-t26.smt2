(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (not (and prt (or (not car) clk))))
(assert (not (not prt)))
(assert (not (not (or (not car) clk))))
(check-sat)
(exit)
