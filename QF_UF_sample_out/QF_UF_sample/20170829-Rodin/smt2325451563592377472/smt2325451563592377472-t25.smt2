(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (not (or (and (not prt) car clk) (and prt (or (not car) clk)) (and (not prt) (or (not car) (not clk))) (and prt car (not clk)))))
(assert (not (not (and prt (or (not car) clk)))))
(check-sat)
(exit)
