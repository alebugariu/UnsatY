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
(assert (! (forall ((x0py0 Int)) (! (= (f (g x0py0)) x0py0) :pattern ((f (g x0py0))) )) :named A0))
(assert (! (= (g 2020) (g 2021)) :named A1))
(check-sat)
(get-info :reason-unknown)