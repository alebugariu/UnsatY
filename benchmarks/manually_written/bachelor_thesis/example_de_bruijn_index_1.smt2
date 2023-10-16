
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Bool Bool Bool Bool) Bool)
(assert (! (forall ((x0 Bool) (x1 Bool) (x2 Bool) (x3 Bool)) (! x1 :pattern ( (f x0 x1 x2 x3)))) :named A0))

(check-sat)
(get-proof)