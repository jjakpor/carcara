(set-logic QF_UF)
(declare-sort utt$8 0)
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$1406 () Bool)
(declare-fun y$1407 () Bool)
(declare-fun y$1437 () Bool)
(declare-fun y$1446 () Bool)
(declare-fun y$15 () Bool)
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
(declare-fun y$7 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$a_Appr_Train_1 () Bool)
(declare-fun y$a_Appr_Train_2 () Bool)
(declare-fun y$a_Cross_Train_1 () Bool)
(declare-fun y$a_Cross_Train_2 () Bool)
(declare-fun y$a_Free () Bool)
(declare-fun y$a_Occ () Bool)
(declare-fun y$a_S1_Clock () Bool)
(declare-fun y$a_S1_Gate () Bool)
(declare-fun y$a_S2 () Bool)
(declare-fun y$a_S3 () Bool)
(declare-fun y$a_S4 () Bool)
(declare-fun y$a_S5 () Bool)
(declare-fun y$a_S6 () Bool)
(declare-fun y$a_Safe_Train_1 () Bool)
(declare-fun y$a_Safe_Train_2 () Bool)
(declare-fun y$a_Send () Bool)
(declare-fun y$a_Shiftdown () Bool)
(declare-fun y$a_Start_IntQueue () Bool)
(declare-fun y$a_Start_Train_1 () Bool)
(declare-fun y$a_Start_Train_2 () Bool)
(declare-fun y$a_Stop_Train_1 () Bool)
(declare-fun y$a_Stop_Train_2 () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id37 () Bool)
(declare-fun y$id37_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n10s32 () utt$32)
(declare-fun y$n15s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n20s8 () utt$8)
(declare-fun y$n25s8 () utt$8)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n5s8 () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$v3_1517448508_35 () Bool)
(declare-fun y$v3_1517448508_35_op () Bool)
(declare-fun y$v_e_0 () utt$8)
(declare-fun y$v_i () utt$8)
(declare-fun y$v_len () utt$8)
(declare-fun y$v_list_0 () utt$8)
(declare-fun y$v_list_1 () utt$8)
(declare-fun y$v_list_2 () utt$8)
(declare-fun y$v_max_x_1 () utt$8)
(declare-fun y$v_max_x_2 () utt$8)
(declare-fun y$v_x () utt$8)
(assert (not (not (and y$a_Cross_Train_1 y$a_Cross_Train_2))))
(assert (not y$a_Cross_Train_1))
(check-sat)
(exit)
