(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-sort L 0)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-fun isEmpty (L) Bool)
(declare-fun contained (L Int) Bool)
(declare-fun indexOf (L Int) Int)
(declare-fun f1 (L) Int)
(declare-const EmptyList L)
(assert (! (forall ((l0py0 L)) (! (or (not (= l0py0 EmptyList)) (isEmpty l0py0)) :pattern ((isEmpty l0py0)) )) :named A0))
(assert (! (forall ((l1py0 L)) (! (or (isEmpty l1py0) (contained l1py0 (f1 l1py0))) :pattern ((isEmpty l1py0)) )) :named A1))
(assert (! (forall ((l2py0 L)) (! (or (not (isEmpty l2py0)) (forall ((el2py0 Int)) (! (not (contained l2py0 el2py0)) :pattern ((contained l2py0 el2py0)) ))) :pattern ((isEmpty l2py0)) )) :named A2))
(assert (! (forall ((l3py0 L)(el3py0 Int)) (! (or (contained l3py0 el3py0) (= (indexOf l3py0 el3py0) (- 1))) :pattern ((contained l3py0 el3py0)) )) :named A3))
(assert (! (forall ((l4py0 L)(el4py0 Int)) (! (<= 0 (indexOf l4py0 el4py0)) :pattern ((indexOf l4py0 el4py0)) )) :named A4))
