(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-fun f (Int) Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-fun g (Int) Int)
(declare-fun h (Int Int) Int)
(assert (! (forall ((xpy0 Int)) (! (= (h (f (g xpy0)) 0) 0) :pattern ((h (g xpy0) xpy0)) )) :named A0))
(assert (! (= (h (f (g 1)) 0) 1) :named A1))
(check-sat)
(get-info :reason-unknown)
