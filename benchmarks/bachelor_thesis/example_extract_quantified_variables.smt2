
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int Int) Int)

(assert (forall ((x0 Int)) (> (f (g x0)) 0)))
(assert (forall ((x1 Int)) (< (f ( + x1 1)) 0)))
(assert (forall ((x2 Int) (x3 Int)) (= (h x2 (+ x3 1)) 0)))

(check-sat)
(get-proof)