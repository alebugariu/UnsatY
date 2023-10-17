(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-fun _div (Int Int) Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(assert (! (forall ((xpy0 Int)(ypy0 Int)) (! (= (to_real (_div xpy0 ypy0)) (/ (to_real xpy0) (to_real ypy0))) :pattern ((_div xpy0 ypy0)) )) :named A0))
