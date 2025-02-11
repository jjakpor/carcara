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
(assert (not (not (= (or (not red_SR) (not (not prt))) (or (not red_SR) prt)))))
(assert (not (not (or (not red_SR) (not (not prt))))))
(assert (not (or (not red_SR) prt)))
(check-sat)
(exit)
