(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(assert (= (= (f a) d) (= d (f a))))
(assert (not (= (not (= (f a) d)) (not (= d (f a))))))
(check-sat)
(exit)
