(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: Aman Goel (amangoel@umich.edu), Karem A. Sakallah (karem@umich.edu)
Generated on: 2018-04-06

Generated by the tool Averroes 2 (successor of [1]) which implements safety property
verification on hardware systems.

This SMT problem belongs to a set of SMT problems generated by applying Averroes 2
to benchmarks derived from [2-5].

A total of 412 systems (345 from [2], 19 from [3], 26 from [4], 22 from [5]) were
syntactically converted from their original formats (using [6, 7]), and given to
Averroes 2 to perform property checking with abstraction (wide bit-vectors -> terms,
wide operators -> UF) using SMT solvers [8, 9].

[1] Lee S., Sakallah K.A. (2014) Unbounded Scalable Verification Based on Approximate
Property-Directed Reachability and Datapath Abstraction. In: Biere A., Bloem R. (eds)
Computer Aided Verification. CAV 2014. Lecture Notes in Computer Science, vol 8559.
Springer, Cham
[2] http://fmv.jku.at/aiger/index.html#beem
[3] http://www.cs.cmu.edu/~modelcheck/vcegar
[4] http://www.cprover.org/hardware/v2c
[5] http://github.com/aman-goel/verilogbench
[6] http://www.clifford.at/yosys
[7] http://github.com/chengyinwu/V3
[8] http://github.com/Z3Prover/z3
[9] http://github.com/SRI-CSL/yices2

id: counter_v
query-maker: "Yices 2"
query-time: 0.002000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: unsat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort utt$4 0)
(declare-fun Add_4_4_4 (utt$4 utt$4) utt$4)
(declare-fun y$13 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$27 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$33 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$43 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$45 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$X () utt$4)
(declare-fun y$X$next () utt$4)
(declare-fun y$X$next_rhs () utt$4)
(declare-fun y$X$next_rhs_op () utt$4)
(declare-fun y$en () Bool)
(declare-fun y$n15s4 () utt$4)
(declare-fun y$n1s4 () utt$4)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$s$1 () utt$4)
(declare-fun y$s$1$next () utt$4)
(declare-fun y$s$1$next_op () utt$4)
(declare-fun y$s$1_op () utt$4)
(declare-fun y$s$4 () utt$4)
(declare-fun y$s$4_op () utt$4)
(assert (not (= y$n1s4 y$n15s4)))
(assert (= y$2 (= y$n1s4 y$X)))
(assert (= (= y$n15s4 y$X) y$6))
(assert (= y$s$1_op (Add_4_4_4 y$X y$n1s4)))
(assert (= y$s$4_op (ite y$6 y$n1s4 y$s$1_op)))
(assert (= y$X$next_rhs_op (ite y$en y$s$4_op y$X)))
(assert (= y$13 (= y$X$next y$X$next_rhs_op)))
(assert (= y$27 (not (= y$n15s4 y$X$next))))
(assert (= y$28 (= y$prop$next y$27)))
(assert (= y$prop$next (not y$26)))
(assert (= y$34 (= y$n1s4 y$X$next)))
(assert (= y$s$1$next_op (Add_4_4_4 y$X$next y$n1s4)))
(assert (= y$37 (= y$n15s4 y$s$1$next_op)))
(assert (= y$43 (and y$34 y$37)))
(assert (= y$43 (not y$45)))
(assert (= y$33 (= y$n15s4 y$s$1_op)))
(assert (= y$42 (and y$2 y$33)))
(assert (= y$42 (not y$44)))
(assert (= y$58 (and y$2 y$13 y$28 y$26 y$45 y$44)))
(assert y$58)
(check-sat)
(exit)
