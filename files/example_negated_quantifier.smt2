; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)

(assert (and (forall ((x0 Int)) (< (f x0) -32)) (forall ((x1 Int) (x2 Int)) (= (f (+ x1 x2)) -32))))

(check-sat)
(get-proof)