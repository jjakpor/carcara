(set-logic QF_UF)
(declare-sort utt$8 0)
(declare-fun y$10 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$18 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$20 () Bool)
(declare-fun y$205 () Bool)
(declare-fun y$215 () Bool)
(declare-fun y$219 () Bool)
(declare-fun y$4 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$L0 () Bool)
(declare-fun y$L1 () Bool)
(declare-fun y$L2 () Bool)
(declare-fun y$L3 () Bool)
(declare-fun y$L4 () Bool)
(declare-fun y$L5 () Bool)
(declare-fun y$L6 () Bool)
(declare-fun y$L7 () Bool)
(declare-fun y$LoneHot () Bool)
(declare-fun y$X () utt$8)
(declare-fun y$Y () utt$8)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n3s8 () utt$8)
(declare-fun y$n4s8 () utt$8)
(declare-fun y$n5s8 () utt$8)
(declare-fun y$prop () Bool)
(assert (not (not (= y$205 (= y$14 y$prop)))))
(assert (not (not y$205)))
(assert (not (= y$14 y$prop)))
(assert (or (not (= y$205 (= y$14 y$prop))) (not y$205) (= y$14 y$prop)))
(check-sat)
(exit)
