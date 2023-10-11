
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)

(assert (forall ((x0 Int) (x1 Int)) (=> (and (= x0 0) (= (f x1) 0)) (forall ((x2 Int)) (< (f x1) x2)))))
(assert (= (f 0) 0))

(check-sat)
(get-proof)