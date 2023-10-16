(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-sort U 0)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)
(declare-fun i (U) U)
(assert (! (forall ((x0py0 U)) (! (= (f x0py0) (h x0py0)) :pattern ((g x0py0)) )) :named A0))
(assert (! (forall ((x1py0 U)) (! (not (= (i (f x1py0)) (i (h x1py0)))) :pattern ((i (f x1py0)) (i (h x1py0))) )) :named A1))
(check-sat)
(get-info :reason-unknown)