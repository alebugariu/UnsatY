
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int Int) Int)

(assert (forall ((x0 Int) (x1 Int) (x2 Int)) (=> (and (> x0 (- 0 1)) (> x1 2)) (and (> (f x0 x1) 7) (<= (f x1 x2) 42)))))
(assert (forall ((x3 Int) (x4 Int)) (=> (and (< x3 1) (< x4 4)) (= (f x3 x4) 6))))

(check-sat)
(get-proof)