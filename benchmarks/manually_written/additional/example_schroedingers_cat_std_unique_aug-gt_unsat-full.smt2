(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-sort cat 0)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-fun alive (cat) Bool)
(assert (! (forall ((x0py0 cat)) (! (alive x0py0) :pattern ((alive x0py0)) )) :named A0))
(assert (! (forall ((x1py0 cat)) (! (not (alive x1py0)) :pattern ((alive x1py0)) )) :named A1))
(check-sat)
(get-info :reason-unknown)