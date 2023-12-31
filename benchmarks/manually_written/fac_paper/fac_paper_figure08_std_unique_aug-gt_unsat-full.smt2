(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-fun f (Int) Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(assert (! (forall ((x0py0 Int)) (! (or (<= x0py0 (- 1)) (not (<= (f x0py0) 7))) :pattern ((f x0py0)) )) :named A0))
(assert (! (forall ((x1py0 Int)) (! (or (<= 1 x1py0) (= (f x1py0) 6)) :pattern ((f x1py0)) )) :named A1))
(check-sat)
(get-info :reason-unknown)