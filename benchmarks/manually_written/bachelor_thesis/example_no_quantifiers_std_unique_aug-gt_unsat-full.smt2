(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-const x0 Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-const x1 Int)
(assert (! false :named A0))
(check-sat)
(get-info :reason-unknown)