
(anchor :step t2)
(assume t2.a0 (= y$n1s4 (ite y$en (ite (= y$n15s4 y$n1s4) y$n1s4 (Add_4_4_4 y$n1s4 y$n1s4)) y$n1s4)))
(assume t2.a1 (= y$n15s4 (ite y$en (ite (= y$n15s4 y$n1s4) y$n1s4 (Add_4_4_4 y$n1s4 y$n1s4)) y$n1s4)))
(assume t2.t226 (= y$n15s4 y$n1s4))
(step t2 (cl (not (= y$n1s4 (ite y$en (ite (= y$n15s4 y$n1s4) y$n1s4 (Add_4_4_4 y$n1s4 y$n1s4)) y$n1s4))) (not (= y$n15s4 (ite y$en (ite (= y$n15s4 y$n1s4) y$n1s4 (Add_4_4_4 y$n1s4 y$n1s4)) y$n1s4))) (= y$n15s4 y$n1s4)) :rule subproof :discharge (t2.a0 t2.a1))
