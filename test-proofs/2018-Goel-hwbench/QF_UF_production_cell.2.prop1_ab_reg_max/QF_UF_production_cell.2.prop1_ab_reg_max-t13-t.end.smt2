(set-logic QF_UF)
(declare-sort utt$8 0)
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$1522 () Bool)
(declare-fun y$1525 () Bool)
(declare-fun y$1526 () Bool)
(declare-fun y$1559 () Bool)
(declare-fun y$1567 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$23 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$27 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$33 () Bool)
(declare-fun y$35 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$39 () Bool)
(declare-fun y$41 () Bool)
(declare-fun y$43 () Bool)
(declare-fun y$45 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$49 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$51 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$55 () Bool)
(declare-fun y$57 () Bool)
(declare-fun y$59 () Bool)
(declare-fun y$62 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$66 () Bool)
(declare-fun y$68 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$70 () Bool)
(declare-fun y$72 () Bool)
(declare-fun y$74 () Bool)
(declare-fun y$76 () Bool)
(declare-fun y$78 () Bool)
(declare-fun y$80 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$a_Apress () Bool)
(declare-fun y$a_Atable () Bool)
(declare-fun y$a_Bdeposit () Bool)
(declare-fun y$a_Bpress () Bool)
(declare-fun y$a_done () Bool)
(declare-fun y$a_down_empty () Bool)
(declare-fun y$a_down_full () Bool)
(declare-fun y$a_got_new () Bool)
(declare-fun y$a_loaded () Bool)
(declare-fun y$a_new_Plate_0 () Bool)
(declare-fun y$a_new_Plate_1 () Bool)
(declare-fun y$a_pressing () Bool)
(declare-fun y$a_q () Bool)
(declare-fun y$a_q1 () Bool)
(declare-fun y$a_q2 () Bool)
(declare-fun y$a_up_empty () Bool)
(declare-fun y$a_up_full () Bool)
(declare-fun y$a_wait_Belt () Bool)
(declare-fun y$a_wait_Deposit () Bool)
(declare-fun y$a_wait_Press () Bool)
(declare-fun y$a_wait_Robot () Bool)
(declare-fun y$a_wait_belt_Plate_0 () Bool)
(declare-fun y$a_wait_belt_Plate_1 () Bool)
(declare-fun y$a_wait_deposit_Plate_0 () Bool)
(declare-fun y$a_wait_deposit_Plate_1 () Bool)
(declare-fun y$a_wait_press_Plate_0 () Bool)
(declare-fun y$a_wait_press_Plate_1 () Bool)
(declare-fun y$a_wait_table_Plate_0 () Bool)
(declare-fun y$a_wait_table_Plate_1 () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id44 () Bool)
(declare-fun y$id44_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n255s8 () utt$8)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n5s8 () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$v_A () utt$8)
(declare-fun y$v_B () utt$8)
(declare-fun y$v_at_press () utt$8)
(declare-fun y$v_at_table () utt$8)
(declare-fun y$v_count () utt$8)
(declare-fun y$v_done () utt$8)
(declare-fun y$v_k_Belt () utt$8)
(declare-fun y$v_k_Deposit () utt$8)
(declare-fun y$v_k_Press () utt$8)
(declare-fun y$v_k_Table () utt$8)
(assert (not (not (= y$66 (= y$v_B y$v_at_press)))))
(assert (not (not y$66)))
(assert (not (= y$v_B y$v_at_press)))
(assert (or (not (= y$66 (= y$v_B y$v_at_press))) (not y$66) (= y$v_B y$v_at_press)))
(check-sat)
(exit)
