
(declare-fun f (Bool Bool Bool Bool) Bool)
(assert (! (forall ((x0 Bool) (x1 Bool) (x2 Bool) (x3 Bool)) (! x2 :pattern ( (f x0 x1 x2 x3)))) :named A0))

(check-sat)
(get-proof)