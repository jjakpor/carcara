(set-logic QF_UF)
(declare-sort utt$8 0)
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$10 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$18 () Bool)
(declare-fun y$20 () Bool)
(declare-fun y$22 () Bool)
(declare-fun y$24 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$629 () Bool)
(declare-fun y$630 () Bool)
(declare-fun y$642 () Bool)
(declare-fun y$649 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$a_done () Bool)
(declare-fun y$a_not_done () Bool)
(declare-fun y$a_q () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id14 () Bool)
(declare-fun y$id14_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n3s8 () utt$8)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$n4s8 () utt$8)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n5s8 () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$v_a_0 () utt$8)
(declare-fun y$v_a_1 () utt$8)
(declare-fun y$v_a_2 () utt$8)
(declare-fun y$v_a_3 () utt$8)
(declare-fun y$v_a_4 () utt$8)
(declare-fun y$v_a_5 () utt$8)
(declare-fun y$v_x () utt$8)
(declare-fun y$v_y () utt$8)
(assert (and y$1 y$3 y$5 y$7 y$10 y$12 y$14 y$16 y$18 y$20 y$22 y$24 y$642 y$630))
(assert (not y$630))
(check-sat)
(exit)
