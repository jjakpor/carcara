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
(assert (not (not (= y$219 (and y$L0 y$2 y$4 y$6 y$8 y$10 y$12 y$14 y$LoneHot y$18 y$20 y$215 y$205)))))
(assert (not (not y$219)))
(assert (not (and y$L0 y$2 y$4 y$6 y$8 y$10 y$12 y$14 y$LoneHot y$18 y$20 y$215 y$205)))
(assert (or (not (= y$219 (and y$L0 y$2 y$4 y$6 y$8 y$10 y$12 y$14 y$LoneHot y$18 y$20 y$215 y$205))) (not y$219) (and y$L0 y$2 y$4 y$6 y$8 y$10 y$12 y$14 y$LoneHot y$18 y$20 y$215 y$205)))
(check-sat)
(exit)
