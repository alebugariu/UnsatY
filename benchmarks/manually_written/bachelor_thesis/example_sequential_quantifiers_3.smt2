
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int Int) Int)

(assert (=> (forall ((x0 Int)) (< (f x0 x0) 0)) (and (forall ((x1 Int) (x2 Int)) (>= (f x1 x2) 0)) (forall ((x3 Int)) (= (f 19 x3) 17)))))
(assert (forall ((x0 Int)) (< (f x0 x0) 0)))

(check-sat)
(get-proof)