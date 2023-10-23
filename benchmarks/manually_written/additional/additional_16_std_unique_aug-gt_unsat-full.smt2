(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-fun increase (Int) Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(assert (! (forall ((x0py0 Int)) (! (>= x0py0 (- 2147483648)) :pattern ((increase x0py0)) )) :named A0))
(assert (! (forall ((x1py0 Int)) (! (<= x1py0 2147483647) :pattern ((increase x1py0)) )) :named A1))
(check-sat)
(get-info :reason-unknown)
