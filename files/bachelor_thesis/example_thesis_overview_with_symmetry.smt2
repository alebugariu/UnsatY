; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int Int) Int)

(assert (forall ((x0 Int) (x1 Int)) (! (=> (and (> x0 (- 0 1)) (> x1 2)) (> (f x0 x1) 7)) :pattern (f x0 x1))))
(assert (forall ((x2 Int) (x3 Int)) (! (=> (and (< x2 1) (< x3 4)) (= (f x2 x3) 6)) :pattern (f x2 x3))))
(assert (forall ((x4 Int) (x5 Int)) (= (f x4 x5) (f x5 x4))))

(check-sat)
(get-proof)