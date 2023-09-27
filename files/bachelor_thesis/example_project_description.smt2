
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)
(assert (forall ((x0 Int)) (! (=> (>= x0 0) (= (f x0) x0)) :pattern (f x0))))
(assert (forall ((x1 Int)) (! (> (f x1) 0) :pattern (f x1))))

(check-sat)
(get-proof)