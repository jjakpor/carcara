(set-logic QF_UF)
(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun prt () Bool)
(assert (= (not (not prt)) prt))
(assert (= (not car) (not car)))
(assert (= (not clk) (not clk)))
(assert (not (= (or (not (not prt)) (not car) (not clk)) (or prt (not car) (not clk)))))
(check-sat)
(exit)
