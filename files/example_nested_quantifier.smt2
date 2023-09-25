; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)

(assert (forall ((x0 Int)) (or (= (f x0) 0) (forall ((x1 Int)) (< (f x0) (+ (f x1) 1))))))
(assert (= (f 0) 1))
(assert (= (f 1) 0))

(check-sat)
(get-proof)