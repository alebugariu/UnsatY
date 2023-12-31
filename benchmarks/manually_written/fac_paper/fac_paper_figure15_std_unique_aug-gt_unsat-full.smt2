(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-fun len (Int) Int)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-fun next (Int) Int)
(assert (! (forall ((x0py0 Int)) (! (not (<= (len x0py0) 0)) :pattern ((len (next x0py0))) )) :named A0))
(assert (! (forall ((x1py0 Int)) (! (or (= (next x1py0) x1py0) (= (len x1py0) (+ 1 (len (next x1py0))))) :pattern ((len (next x1py0))) )) :named A1))
(assert (! (forall ((x2py0 Int)) (! (or (not (= (next x2py0) x2py0)) (= (len x2py0) 1)) :pattern ((len (next x2py0))) )) :named A2))
(assert (! (<= (len 7) 0) :named A3))
(check-sat)
(get-info :reason-unknown)