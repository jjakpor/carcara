(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
http://www.cs.bham.ac.uk/~vxs/quasigroups/benchmark/

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-sort I 0)
(declare-fun op1 (I I) I)
(declare-fun op (I I) I)
(declare-fun e4 () I)
(declare-fun e3 () I)
(declare-fun e2 () I)
(declare-fun e1 () I)
(declare-fun e0 () I)
(assert (and (and (and (and (and (and (and (and (or (or (or (or (= (op e0 e0) e0) (= (op e0 e0) e1)) (= (op e0 e0) e2)) (= (op e0 e0) e3)) (= (op e0 e0) e4)) (or (or (or (or (= (op e0 e1) e0) (= (op e0 e1) e1)) (= (op e0 e1) e2)) (= (op e0 e1) e3)) (= (op e0 e1) e4))) (or (or (or (or (= (op e0 e2) e0) (= (op e0 e2) e1)) (= (op e0 e2) e2)) (= (op e0 e2) e3)) (= (op e0 e2) e4))) (or (or (or (or (= (op e0 e3) e0) (= (op e0 e3) e1)) (= (op e0 e3) e2)) (= (op e0 e3) e3)) (= (op e0 e3) e4))) (or (or (or (or (= (op e0 e4) e0) (= (op e0 e4) e1)) (= (op e0 e4) e2)) (= (op e0 e4) e3)) (= (op e0 e4) e4))) (and (and (and (and (or (or (or (or (= (op e1 e0) e0) (= (op e1 e0) e1)) (= (op e1 e0) e2)) (= (op e1 e0) e3)) (= (op e1 e0) e4)) (or (or (or (or (= (op e1 e1) e0) (= (op e1 e1) e1)) (= (op e1 e1) e2)) (= (op e1 e1) e3)) (= (op e1 e1) e4))) (or (or (or (or (= (op e1 e2) e0) (= (op e1 e2) e1)) (= (op e1 e2) e2)) (= (op e1 e2) e3)) (= (op e1 e2) e4))) (or (or (or (or (= (op e1 e3) e0) (= (op e1 e3) e1)) (= (op e1 e3) e2)) (= (op e1 e3) e3)) (= (op e1 e3) e4))) (or (or (or (or (= (op e1 e4) e0) (= (op e1 e4) e1)) (= (op e1 e4) e2)) (= (op e1 e4) e3)) (= (op e1 e4) e4)))) (and (and (and (and (or (or (or (or (= (op e2 e0) e0) (= (op e2 e0) e1)) (= (op e2 e0) e2)) (= (op e2 e0) e3)) (= (op e2 e0) e4)) (or (or (or (or (= (op e2 e1) e0) (= (op e2 e1) e1)) (= (op e2 e1) e2)) (= (op e2 e1) e3)) (= (op e2 e1) e4))) (or (or (or (or (= (op e2 e2) e0) (= (op e2 e2) e1)) (= (op e2 e2) e2)) (= (op e2 e2) e3)) (= (op e2 e2) e4))) (or (or (or (or (= (op e2 e3) e0) (= (op e2 e3) e1)) (= (op e2 e3) e2)) (= (op e2 e3) e3)) (= (op e2 e3) e4))) (or (or (or (or (= (op e2 e4) e0) (= (op e2 e4) e1)) (= (op e2 e4) e2)) (= (op e2 e4) e3)) (= (op e2 e4) e4)))) (and (and (and (and (or (or (or (or (= (op e3 e0) e0) (= (op e3 e0) e1)) (= (op e3 e0) e2)) (= (op e3 e0) e3)) (= (op e3 e0) e4)) (or (or (or (or (= (op e3 e1) e0) (= (op e3 e1) e1)) (= (op e3 e1) e2)) (= (op e3 e1) e3)) (= (op e3 e1) e4))) (or (or (or (or (= (op e3 e2) e0) (= (op e3 e2) e1)) (= (op e3 e2) e2)) (= (op e3 e2) e3)) (= (op e3 e2) e4))) (or (or (or (or (= (op e3 e3) e0) (= (op e3 e3) e1)) (= (op e3 e3) e2)) (= (op e3 e3) e3)) (= (op e3 e3) e4))) (or (or (or (or (= (op e3 e4) e0) (= (op e3 e4) e1)) (= (op e3 e4) e2)) (= (op e3 e4) e3)) (= (op e3 e4) e4)))) (and (and (and (and (or (or (or (or (= (op e4 e0) e0) (= (op e4 e0) e1)) (= (op e4 e0) e2)) (= (op e4 e0) e3)) (= (op e4 e0) e4)) (or (or (or (or (= (op e4 e1) e0) (= (op e4 e1) e1)) (= (op e4 e1) e2)) (= (op e4 e1) e3)) (= (op e4 e1) e4))) (or (or (or (or (= (op e4 e2) e0) (= (op e4 e2) e1)) (= (op e4 e2) e2)) (= (op e4 e2) e3)) (= (op e4 e2) e4))) (or (or (or (or (= (op e4 e3) e0) (= (op e4 e3) e1)) (= (op e4 e3) e2)) (= (op e4 e3) e3)) (= (op e4 e3) e4))) (or (or (or (or (= (op e4 e4) e0) (= (op e4 e4) e1)) (= (op e4 e4) e2)) (= (op e4 e4) e3)) (= (op e4 e4) e4)))))
(assert (and (and (and (and (and (and (and (and (and (or (or (or (or (= (op e0 e0) e0) (= (op e0 e1) e0)) (= (op e0 e2) e0)) (= (op e0 e3) e0)) (= (op e0 e4) e0)) (or (or (or (or (= (op e0 e0) e0) (= (op e1 e0) e0)) (= (op e2 e0) e0)) (= (op e3 e0) e0)) (= (op e4 e0) e0))) (and (or (or (or (or (= (op e0 e0) e1) (= (op e0 e1) e1)) (= (op e0 e2) e1)) (= (op e0 e3) e1)) (= (op e0 e4) e1)) (or (or (or (or (= (op e0 e0) e1) (= (op e1 e0) e1)) (= (op e2 e0) e1)) (= (op e3 e0) e1)) (= (op e4 e0) e1)))) (and (or (or (or (or (= (op e0 e0) e2) (= (op e0 e1) e2)) (= (op e0 e2) e2)) (= (op e0 e3) e2)) (= (op e0 e4) e2)) (or (or (or (or (= (op e0 e0) e2) (= (op e1 e0) e2)) (= (op e2 e0) e2)) (= (op e3 e0) e2)) (= (op e4 e0) e2)))) (and (or (or (or (or (= (op e0 e0) e3) (= (op e0 e1) e3)) (= (op e0 e2) e3)) (= (op e0 e3) e3)) (= (op e0 e4) e3)) (or (or (or (or (= (op e0 e0) e3) (= (op e1 e0) e3)) (= (op e2 e0) e3)) (= (op e3 e0) e3)) (= (op e4 e0) e3)))) (and (or (or (or (or (= (op e0 e0) e4) (= (op e0 e1) e4)) (= (op e0 e2) e4)) (= (op e0 e3) e4)) (= (op e0 e4) e4)) (or (or (or (or (= (op e0 e0) e4) (= (op e1 e0) e4)) (= (op e2 e0) e4)) (= (op e3 e0) e4)) (= (op e4 e0) e4)))) (and (and (and (and (and (or (or (or (or (= (op e1 e0) e0) (= (op e1 e1) e0)) (= (op e1 e2) e0)) (= (op e1 e3) e0)) (= (op e1 e4) e0)) (or (or (or (or (= (op e0 e1) e0) (= (op e1 e1) e0)) (= (op e2 e1) e0)) (= (op e3 e1) e0)) (= (op e4 e1) e0))) (and (or (or (or (or (= (op e1 e0) e1) (= (op e1 e1) e1)) (= (op e1 e2) e1)) (= (op e1 e3) e1)) (= (op e1 e4) e1)) (or (or (or (or (= (op e0 e1) e1) (= (op e1 e1) e1)) (= (op e2 e1) e1)) (= (op e3 e1) e1)) (= (op e4 e1) e1)))) (and (or (or (or (or (= (op e1 e0) e2) (= (op e1 e1) e2)) (= (op e1 e2) e2)) (= (op e1 e3) e2)) (= (op e1 e4) e2)) (or (or (or (or (= (op e0 e1) e2) (= (op e1 e1) e2)) (= (op e2 e1) e2)) (= (op e3 e1) e2)) (= (op e4 e1) e2)))) (and (or (or (or (or (= (op e1 e0) e3) (= (op e1 e1) e3)) (= (op e1 e2) e3)) (= (op e1 e3) e3)) (= (op e1 e4) e3)) (or (or (or (or (= (op e0 e1) e3) (= (op e1 e1) e3)) (= (op e2 e1) e3)) (= (op e3 e1) e3)) (= (op e4 e1) e3)))) (and (or (or (or (or (= (op e1 e0) e4) (= (op e1 e1) e4)) (= (op e1 e2) e4)) (= (op e1 e3) e4)) (= (op e1 e4) e4)) (or (or (or (or (= (op e0 e1) e4) (= (op e1 e1) e4)) (= (op e2 e1) e4)) (= (op e3 e1) e4)) (= (op e4 e1) e4))))) (and (and (and (and (and (or (or (or (or (= (op e2 e0) e0) (= (op e2 e1) e0)) (= (op e2 e2) e0)) (= (op e2 e3) e0)) (= (op e2 e4) e0)) (or (or (or (or (= (op e0 e2) e0) (= (op e1 e2) e0)) (= (op e2 e2) e0)) (= (op e3 e2) e0)) (= (op e4 e2) e0))) (and (or (or (or (or (= (op e2 e0) e1) (= (op e2 e1) e1)) (= (op e2 e2) e1)) (= (op e2 e3) e1)) (= (op e2 e4) e1)) (or (or (or (or (= (op e0 e2) e1) (= (op e1 e2) e1)) (= (op e2 e2) e1)) (= (op e3 e2) e1)) (= (op e4 e2) e1)))) (and (or (or (or (or (= (op e2 e0) e2) (= (op e2 e1) e2)) (= (op e2 e2) e2)) (= (op e2 e3) e2)) (= (op e2 e4) e2)) (or (or (or (or (= (op e0 e2) e2) (= (op e1 e2) e2)) (= (op e2 e2) e2)) (= (op e3 e2) e2)) (= (op e4 e2) e2)))) (and (or (or (or (or (= (op e2 e0) e3) (= (op e2 e1) e3)) (= (op e2 e2) e3)) (= (op e2 e3) e3)) (= (op e2 e4) e3)) (or (or (or (or (= (op e0 e2) e3) (= (op e1 e2) e3)) (= (op e2 e2) e3)) (= (op e3 e2) e3)) (= (op e4 e2) e3)))) (and (or (or (or (or (= (op e2 e0) e4) (= (op e2 e1) e4)) (= (op e2 e2) e4)) (= (op e2 e3) e4)) (= (op e2 e4) e4)) (or (or (or (or (= (op e0 e2) e4) (= (op e1 e2) e4)) (= (op e2 e2) e4)) (= (op e3 e2) e4)) (= (op e4 e2) e4))))) (and (and (and (and (and (or (or (or (or (= (op e3 e0) e0) (= (op e3 e1) e0)) (= (op e3 e2) e0)) (= (op e3 e3) e0)) (= (op e3 e4) e0)) (or (or (or (or (= (op e0 e3) e0) (= (op e1 e3) e0)) (= (op e2 e3) e0)) (= (op e3 e3) e0)) (= (op e4 e3) e0))) (and (or (or (or (or (= (op e3 e0) e1) (= (op e3 e1) e1)) (= (op e3 e2) e1)) (= (op e3 e3) e1)) (= (op e3 e4) e1)) (or (or (or (or (= (op e0 e3) e1) (= (op e1 e3) e1)) (= (op e2 e3) e1)) (= (op e3 e3) e1)) (= (op e4 e3) e1)))) (and (or (or (or (or (= (op e3 e0) e2) (= (op e3 e1) e2)) (= (op e3 e2) e2)) (= (op e3 e3) e2)) (= (op e3 e4) e2)) (or (or (or (or (= (op e0 e3) e2) (= (op e1 e3) e2)) (= (op e2 e3) e2)) (= (op e3 e3) e2)) (= (op e4 e3) e2)))) (and (or (or (or (or (= (op e3 e0) e3) (= (op e3 e1) e3)) (= (op e3 e2) e3)) (= (op e3 e3) e3)) (= (op e3 e4) e3)) (or (or (or (or (= (op e0 e3) e3) (= (op e1 e3) e3)) (= (op e2 e3) e3)) (= (op e3 e3) e3)) (= (op e4 e3) e3)))) (and (or (or (or (or (= (op e3 e0) e4) (= (op e3 e1) e4)) (= (op e3 e2) e4)) (= (op e3 e3) e4)) (= (op e3 e4) e4)) (or (or (or (or (= (op e0 e3) e4) (= (op e1 e3) e4)) (= (op e2 e3) e4)) (= (op e3 e3) e4)) (= (op e4 e3) e4))))) (and (and (and (and (and (or (or (or (or (= (op e4 e0) e0) (= (op e4 e1) e0)) (= (op e4 e2) e0)) (= (op e4 e3) e0)) (= (op e4 e4) e0)) (or (or (or (or (= (op e0 e4) e0) (= (op e1 e4) e0)) (= (op e2 e4) e0)) (= (op e3 e4) e0)) (= (op e4 e4) e0))) (and (or (or (or (or (= (op e4 e0) e1) (= (op e4 e1) e1)) (= (op e4 e2) e1)) (= (op e4 e3) e1)) (= (op e4 e4) e1)) (or (or (or (or (= (op e0 e4) e1) (= (op e1 e4) e1)) (= (op e2 e4) e1)) (= (op e3 e4) e1)) (= (op e4 e4) e1)))) (and (or (or (or (or (= (op e4 e0) e2) (= (op e4 e1) e2)) (= (op e4 e2) e2)) (= (op e4 e3) e2)) (= (op e4 e4) e2)) (or (or (or (or (= (op e0 e4) e2) (= (op e1 e4) e2)) (= (op e2 e4) e2)) (= (op e3 e4) e2)) (= (op e4 e4) e2)))) (and (or (or (or (or (= (op e4 e0) e3) (= (op e4 e1) e3)) (= (op e4 e2) e3)) (= (op e4 e3) e3)) (= (op e4 e4) e3)) (or (or (or (or (= (op e0 e4) e3) (= (op e1 e4) e3)) (= (op e2 e4) e3)) (= (op e3 e4) e3)) (= (op e4 e4) e3)))) (and (or (or (or (or (= (op e4 e0) e4) (= (op e4 e1) e4)) (= (op e4 e2) e4)) (= (op e4 e3) e4)) (= (op e4 e4) e4)) (or (or (or (or (= (op e0 e4) e4) (= (op e1 e4) e4)) (= (op e2 e4) e4)) (= (op e3 e4) e4)) (= (op e4 e4) e4))))))
(assert (and (and (and (and (or (or (or (or (= (op e0 e0) e0) (= (op e1 e1) e0)) (= (op e2 e2) e0)) (= (op e3 e3) e0)) (= (op e4 e4) e0)) (or (or (or (or (= (op e0 e0) e1) (= (op e1 e1) e1)) (= (op e2 e2) e1)) (= (op e3 e3) e1)) (= (op e4 e4) e1))) (or (or (or (or (= (op e0 e0) e2) (= (op e1 e1) e2)) (= (op e2 e2) e2)) (= (op e3 e3) e2)) (= (op e4 e4) e2))) (or (or (or (or (= (op e0 e0) e3) (= (op e1 e1) e3)) (= (op e2 e2) e3)) (= (op e3 e3) e3)) (= (op e4 e4) e3))) (or (or (or (or (= (op e0 e0) e4) (= (op e1 e1) e4)) (= (op e2 e2) e4)) (= (op e3 e3) e4)) (= (op e4 e4) e4))))
(assert (and (and (and (and (or (or (or (or (= (op e0 e0) e0) (= (op e1 e0) e1)) (= (op e2 e0) e2)) (= (op e3 e0) e3)) (= (op e4 e0) e4)) (or (or (or (or (= (op e0 e1) e0) (= (op e1 e1) e1)) (= (op e2 e1) e2)) (= (op e3 e1) e3)) (= (op e4 e1) e4))) (or (or (or (or (= (op e0 e2) e0) (= (op e1 e2) e1)) (= (op e2 e2) e2)) (= (op e3 e2) e3)) (= (op e4 e2) e4))) (or (or (or (or (= (op e0 e3) e0) (= (op e1 e3) e1)) (= (op e2 e3) e2)) (= (op e3 e3) e3)) (= (op e4 e3) e4))) (or (or (or (or (= (op e0 e4) e0) (= (op e1 e4) e1)) (= (op e2 e4) e2)) (= (op e3 e4) e3)) (= (op e4 e4) e4))))
(assert (or (or (or (or (or (or (or (or (not (= (op e0 e0) (op e0 e0))) (not (= (op e1 e0) (op e0 e1)))) (not (= (op e2 e0) (op e0 e2)))) (not (= (op e3 e0) (op e0 e3)))) (not (= (op e4 e0) (op e0 e4)))) (or (or (or (or (not (= (op e0 e1) (op e1 e0))) (not (= (op e1 e1) (op e1 e1)))) (not (= (op e2 e1) (op e1 e2)))) (not (= (op e3 e1) (op e1 e3)))) (not (= (op e4 e1) (op e1 e4))))) (or (or (or (or (not (= (op e0 e2) (op e2 e0))) (not (= (op e1 e2) (op e2 e1)))) (not (= (op e2 e2) (op e2 e2)))) (not (= (op e3 e2) (op e2 e3)))) (not (= (op e4 e2) (op e2 e4))))) (or (or (or (or (not (= (op e0 e3) (op e3 e0))) (not (= (op e1 e3) (op e3 e1)))) (not (= (op e2 e3) (op e3 e2)))) (not (= (op e3 e3) (op e3 e3)))) (not (= (op e4 e3) (op e3 e4))))) (or (or (or (or (not (= (op e0 e4) (op e4 e0))) (not (= (op e1 e4) (op e4 e1)))) (not (= (op e2 e4) (op e4 e2)))) (not (= (op e3 e4) (op e4 e3)))) (not (= (op e4 e4) (op e4 e4))))))
(assert (or (or (or (or (= (op e0 e0) e0) (= (op e1 e1) e1)) (= (op e2 e2) e2)) (= (op e3 e3) e3)) (= (op e4 e4) e4)))
(assert (and (and (and (and (and (and (and (and (= (op e0 (op e0 e0)) e0) (= (op e0 (op e0 e1)) e1)) (= (op e0 (op e0 e2)) e2)) (= (op e0 (op e0 e3)) e3)) (= (op e0 (op e0 e4)) e4)) (and (and (and (and (= (op e1 (op e1 e0)) e0) (= (op e1 (op e1 e1)) e1)) (= (op e1 (op e1 e2)) e2)) (= (op e1 (op e1 e3)) e3)) (= (op e1 (op e1 e4)) e4))) (and (and (and (and (= (op e2 (op e2 e0)) e0) (= (op e2 (op e2 e1)) e1)) (= (op e2 (op e2 e2)) e2)) (= (op e2 (op e2 e3)) e3)) (= (op e2 (op e2 e4)) e4))) (and (and (and (and (= (op e3 (op e3 e0)) e0) (= (op e3 (op e3 e1)) e1)) (= (op e3 (op e3 e2)) e2)) (= (op e3 (op e3 e3)) e3)) (= (op e3 (op e3 e4)) e4))) (and (and (and (and (= (op e4 (op e4 e0)) e0) (= (op e4 (op e4 e1)) e1)) (= (op e4 (op e4 e2)) e2)) (= (op e4 (op e4 e3)) e3)) (= (op e4 (op e4 e4)) e4))))
(assert (and (and (and (and (= (op e0 e0) e0) (= (op e1 e1) e1)) (= (op e2 e2) e2)) (= (op e3 e3) e3)) (= (op e4 e4) e4)))
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (= (op e0 e0) (op e1 e0))) (not (= (op e0 e0) (op e2 e0)))) (not (= (op e0 e0) (op e3 e0)))) (not (= (op e0 e0) (op e4 e0)))) (not (= (op e1 e0) (op e2 e0)))) (not (= (op e1 e0) (op e3 e0)))) (not (= (op e1 e0) (op e4 e0)))) (not (= (op e2 e0) (op e3 e0)))) (not (= (op e2 e0) (op e4 e0)))) (not (= (op e3 e0) (op e4 e0)))) (and (and (and (and (and (and (and (and (and (not (= (op e0 e1) (op e1 e1))) (not (= (op e0 e1) (op e2 e1)))) (not (= (op e0 e1) (op e3 e1)))) (not (= (op e0 e1) (op e4 e1)))) (not (= (op e1 e1) (op e2 e1)))) (not (= (op e1 e1) (op e3 e1)))) (not (= (op e1 e1) (op e4 e1)))) (not (= (op e2 e1) (op e3 e1)))) (not (= (op e2 e1) (op e4 e1)))) (not (= (op e3 e1) (op e4 e1))))) (and (and (and (and (and (and (and (and (and (not (= (op e0 e2) (op e1 e2))) (not (= (op e0 e2) (op e2 e2)))) (not (= (op e0 e2) (op e3 e2)))) (not (= (op e0 e2) (op e4 e2)))) (not (= (op e1 e2) (op e2 e2)))) (not (= (op e1 e2) (op e3 e2)))) (not (= (op e1 e2) (op e4 e2)))) (not (= (op e2 e2) (op e3 e2)))) (not (= (op e2 e2) (op e4 e2)))) (not (= (op e3 e2) (op e4 e2))))) (and (and (and (and (and (and (and (and (and (not (= (op e0 e3) (op e1 e3))) (not (= (op e0 e3) (op e2 e3)))) (not (= (op e0 e3) (op e3 e3)))) (not (= (op e0 e3) (op e4 e3)))) (not (= (op e1 e3) (op e2 e3)))) (not (= (op e1 e3) (op e3 e3)))) (not (= (op e1 e3) (op e4 e3)))) (not (= (op e2 e3) (op e3 e3)))) (not (= (op e2 e3) (op e4 e3)))) (not (= (op e3 e3) (op e4 e3))))) (and (and (and (and (and (and (and (and (and (not (= (op e0 e4) (op e1 e4))) (not (= (op e0 e4) (op e2 e4)))) (not (= (op e0 e4) (op e3 e4)))) (not (= (op e0 e4) (op e4 e4)))) (not (= (op e1 e4) (op e2 e4)))) (not (= (op e1 e4) (op e3 e4)))) (not (= (op e1 e4) (op e4 e4)))) (not (= (op e2 e4) (op e3 e4)))) (not (= (op e2 e4) (op e4 e4)))) (not (= (op e3 e4) (op e4 e4))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (not (= (op e0 e0) (op e0 e1))) (not (= (op e0 e0) (op e0 e2)))) (not (= (op e0 e0) (op e0 e3)))) (not (= (op e0 e0) (op e0 e4)))) (not (= (op e0 e1) (op e0 e2)))) (not (= (op e0 e1) (op e0 e3)))) (not (= (op e0 e1) (op e0 e4)))) (not (= (op e0 e2) (op e0 e3)))) (not (= (op e0 e2) (op e0 e4)))) (not (= (op e0 e3) (op e0 e4)))) (and (and (and (and (and (and (and (and (and (not (= (op e1 e0) (op e1 e1))) (not (= (op e1 e0) (op e1 e2)))) (not (= (op e1 e0) (op e1 e3)))) (not (= (op e1 e0) (op e1 e4)))) (not (= (op e1 e1) (op e1 e2)))) (not (= (op e1 e1) (op e1 e3)))) (not (= (op e1 e1) (op e1 e4)))) (not (= (op e1 e2) (op e1 e3)))) (not (= (op e1 e2) (op e1 e4)))) (not (= (op e1 e3) (op e1 e4))))) (and (and (and (and (and (and (and (and (and (not (= (op e2 e0) (op e2 e1))) (not (= (op e2 e0) (op e2 e2)))) (not (= (op e2 e0) (op e2 e3)))) (not (= (op e2 e0) (op e2 e4)))) (not (= (op e2 e1) (op e2 e2)))) (not (= (op e2 e1) (op e2 e3)))) (not (= (op e2 e1) (op e2 e4)))) (not (= (op e2 e2) (op e2 e3)))) (not (= (op e2 e2) (op e2 e4)))) (not (= (op e2 e3) (op e2 e4))))) (and (and (and (and (and (and (and (and (and (not (= (op e3 e0) (op e3 e1))) (not (= (op e3 e0) (op e3 e2)))) (not (= (op e3 e0) (op e3 e3)))) (not (= (op e3 e0) (op e3 e4)))) (not (= (op e3 e1) (op e3 e2)))) (not (= (op e3 e1) (op e3 e3)))) (not (= (op e3 e1) (op e3 e4)))) (not (= (op e3 e2) (op e3 e3)))) (not (= (op e3 e2) (op e3 e4)))) (not (= (op e3 e3) (op e3 e4))))) (and (and (and (and (and (and (and (and (and (not (= (op e4 e0) (op e4 e1))) (not (= (op e4 e0) (op e4 e2)))) (not (= (op e4 e0) (op e4 e3)))) (not (= (op e4 e0) (op e4 e4)))) (not (= (op e4 e1) (op e4 e2)))) (not (= (op e4 e1) (op e4 e3)))) (not (= (op e4 e1) (op e4 e4)))) (not (= (op e4 e2) (op e4 e3)))) (not (= (op e4 e2) (op e4 e4)))) (not (= (op e4 e3) (op e4 e4)))))))
(assert (and (and (and (and (and (and (and (and (and (not (= e0 e1)) (not (= e0 e2))) (not (= e0 e3))) (not (= e0 e4))) (not (= e1 e2))) (not (= e1 e3))) (not (= e1 e4))) (not (= e2 e3))) (not (= e2 e4))) (not (= e3 e4))))
(assert (and (and (= e0 (op e2 e1)) (= e2 (op e1 e3))) (= e4 (op e2 e3))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (op e0 e0) e0) (= (op e0 e1) e3)) (= (op e0 e2) e4)) (= (op e0 e3) e1)) (= (op e0 e4) e2)) (= (op e1 e0) e4)) (= (op e1 e1) e1)) (= (op e1 e2) e3)) (= (op e1 e3) e2)) (= (op e1 e4) e0)) (= (op e2 e0) e1)) (= (op e2 e1) e0)) (= (op e2 e2) e2)) (= (op e2 e3) e4)) (= (op e2 e4) e3)) (= (op e3 e0) e2)) (= (op e3 e1) e4)) (= (op e3 e2) e0)) (= (op e3 e3) e3)) (= (op e3 e4) e1)) (= (op e4 e0) e3)) (= (op e4 e1) e2)) (= (op e4 e2) e1)) (= (op e4 e3) e0)) (= (op e4 e4) e4))))
(check-sat)
(exit)
