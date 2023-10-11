
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Bool Bool) Bool)
(assert (! (forall ((x0 Bool) (y0 Bool)) (! (and x0 y0) :pattern ((f x0 y0)))) :named A0))

(check-sat)
(get-proof)