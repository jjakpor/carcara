(set-logic QF_UF)
(declare-sort utt$4 0)
(declare-fun Add_4_4_4 (utt$4 utt$4) utt$4)
(declare-fun y$13 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$27 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$33 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$43 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$45 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$X () utt$4)
(declare-fun y$X$next () utt$4)
(declare-fun y$X$next_rhs () utt$4)
(declare-fun y$X$next_rhs_op () utt$4)
(declare-fun y$en () Bool)
(declare-fun y$n15s4 () utt$4)
(declare-fun y$n1s4 () utt$4)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$s$1 () utt$4)
(declare-fun y$s$1$next () utt$4)
(declare-fun y$s$1$next_op () utt$4)
(declare-fun y$s$1_op () utt$4)
(declare-fun y$s$4 () utt$4)
(declare-fun y$s$4_op () utt$4)
(assert (= y$27 (not (= y$X$next y$n15s4))))
(assert (= y$prop$next y$prop$next))
(assert (not (= (= y$27 y$prop$next) (= (not (= y$X$next y$n15s4)) y$prop$next))))
(check-sat)
(exit)
