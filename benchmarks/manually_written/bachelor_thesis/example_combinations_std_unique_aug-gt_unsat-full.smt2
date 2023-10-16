(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-fun f (Int Int) Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(assert (! (forall ((x0py0 Int)(x1py0 Int)) (! (= (f x0py0 x1py0) (f x1py0 x0py0)) :pattern ((f x0py0 x1py0)) :pattern ((f x1py0 x0py0)) )) :named A0))
(assert (! (not (= (f 2 3) (f 3 2))) :named A1))
