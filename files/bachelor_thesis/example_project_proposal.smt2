
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)
(assert (forall ((x0 Int)) (=> (> x0 -1) (> (f x0) 7))))
(assert (forall ((x1 Int)) (=> (< x1 1) (= (f x1) 6))))

(check-sat)
(get-proof)