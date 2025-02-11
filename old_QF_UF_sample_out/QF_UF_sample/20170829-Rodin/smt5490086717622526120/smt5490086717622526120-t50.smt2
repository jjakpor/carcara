(set-logic QF_UF)
(declare-fun circuit () Bool)
(declare-fun grn () Bool)
(declare-fun grn_MR () Bool)
(declare-fun grn_SR () Bool)
(declare-fun org () Bool)
(declare-fun org_MR () Bool)
(declare-fun org_SR () Bool)
(declare-fun prt () Bool)
(declare-fun rd1 () Bool)
(declare-fun rd2 () Bool)
(declare-fun red_MR () Bool)
(declare-fun red_SR () Bool)
(assert (not (or (and prt red_SR) (and (not prt) red_MR) (and red_SR (not prt)) (and red_MR prt))))
(assert (not (not (and prt red_SR))))
(check-sat)
(exit)
