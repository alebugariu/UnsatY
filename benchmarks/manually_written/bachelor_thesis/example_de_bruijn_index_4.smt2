
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Bool) Bool)
(assert (forall ((x0 Bool)) (! (or (not x0) (forall ((x1 Bool)) x1)) :pattern ((f x0)))))

(check-sat)
(get-proof)