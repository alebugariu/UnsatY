(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-sort U 0)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-fun f (U U) Int)
(declare-fun a () U)
(declare-fun b () U)
(assert (! (forall ((x0py0 U)(y0py0 U)) (! (or (= x0py0 y0py0) (= (f x0py0 y0py0) 0)) :pattern ((f x0py0 y0py0)) )) :named A0))
(assert (! (forall ((x1py0 U)(y1py0 U)) (! (or (not (= x1py0 a)) (not (= y1py0 b)) (= (f x1py0 y1py0) 1)) :pattern ((f x1py0 y1py0)) )) :named A1))
(assert (! (not (= a b)) :named A2))
