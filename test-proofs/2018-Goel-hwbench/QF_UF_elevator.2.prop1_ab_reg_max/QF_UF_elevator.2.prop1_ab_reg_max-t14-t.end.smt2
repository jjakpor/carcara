(set-logic QF_UF)
(declare-sort utt$8 0)
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$1517 () Bool)
(declare-fun y$1518 () Bool)
(declare-fun y$1557 () Bool)
(declare-fun y$1566 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$23 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$36 () Bool)
(declare-fun y$38 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$46 () Bool)
(declare-fun y$48 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$50 () Bool)
(declare-fun y$52 () Bool)
(declare-fun y$54 () Bool)
(declare-fun y$56 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$60 () Bool)
(declare-fun y$62 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$66 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$a_choose_next () Bool)
(declare-fun y$a_in_elevator_Person_0 () Bool)
(declare-fun y$a_in_elevator_Person_1 () Bool)
(declare-fun y$a_move_next () Bool)
(declare-fun y$a_out_Person_0 () Bool)
(declare-fun y$a_out_Person_1 () Bool)
(declare-fun y$a_q_Elevator () Bool)
(declare-fun y$a_q_Servis () Bool)
(declare-fun y$a_r () Bool)
(declare-fun y$a_transporting () Bool)
(declare-fun y$a_waiting_Person_0 () Bool)
(declare-fun y$a_waiting_Person_1 () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id36 () Bool)
(declare-fun y$id36_op () Bool)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n3s8 () utt$8)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$prop () Bool)
(declare-fun y$v3_1517448494_34 () Bool)
(declare-fun y$v3_1517448494_34_op () Bool)
(declare-fun y$v_at_floor_Person_0 () utt$8)
(declare-fun y$v_at_floor_Person_1 () utt$8)
(declare-fun y$v_caller () utt$8)
(declare-fun y$v_current () utt$8)
(declare-fun y$v_floor () utt$8)
(declare-fun y$v_floor_queue_0_0 () utt$8)
(declare-fun y$v_floor_queue_0_1 () utt$8)
(declare-fun y$v_floor_queue_0_act () utt$8)
(declare-fun y$v_floor_queue_1_0 () utt$8)
(declare-fun y$v_floor_queue_1_1 () utt$8)
(declare-fun y$v_floor_queue_1_act () utt$8)
(declare-fun y$v_floor_queue_2_0 () utt$8)
(declare-fun y$v_floor_queue_2_1 () utt$8)
(declare-fun y$v_floor_queue_2_act () utt$8)
(declare-fun y$v_floor_queue_3_0 () utt$8)
(declare-fun y$v_floor_queue_3_1 () utt$8)
(declare-fun y$v_floor_queue_3_act () utt$8)
(declare-fun y$v_going_to () utt$8)
(declare-fun y$v_serving () utt$8)
(declare-fun y$v_who () utt$8)
(assert (not (not y$prop)))
(assert (not (not y$1557)))
(assert (or (not y$prop) (not y$1557)))
(check-sat)
(exit)
