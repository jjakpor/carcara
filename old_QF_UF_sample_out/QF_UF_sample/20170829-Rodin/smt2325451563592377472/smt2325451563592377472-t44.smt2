(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (not (or (not (not prt)) (not car) (not clk))))
(assert (not (not (not clk))))
(check-sat)
(exit)
