
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int Int) Int)

(assert (forall ((x0 Int) (x1 Int)) (= (f x0 x1) (f x1 x0))))
(assert (not (= (f 2 3) (f 3 2))))

(check-sat)
(get-proof)