(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-fun f (Bool Bool Bool Bool) Bool)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(assert (! (forall ((x0py0 Bool)(x1py0 Bool)(x2py0 Bool)(x3py0 Bool)) (! x0py0 :pattern ((f x0py0 x1py0 x2py0 x3py0)) )) :named A0))
(check-sat)
(get-info :reason-unknown)