(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(assert (not (not (= (or (not (= d (f b))) (not (not (= d (f a))))) (or (not (= d (f b))) (= d (f a)))))))
(assert (not (not (or (not (= d (f b))) (not (not (= d (f a))))))))
(assert (not (or (not (= d (f b))) (= d (f a)))))
(check-sat)
(exit)
