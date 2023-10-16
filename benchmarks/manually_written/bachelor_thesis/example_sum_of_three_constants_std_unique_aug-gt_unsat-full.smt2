(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-const x Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-const y Int)
(declare-const z Int)
(assert (! (not (<= 0 x)) :named A0))
(assert (! (not (<= 0 y)) :named A1))
(assert (! (not (<= 0 z)) :named A2))
(assert (! (<= 0 (+ x y z)) :named A3))
