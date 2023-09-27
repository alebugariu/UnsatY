; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int Int) Int)

(assert (forall ((x Int)) (= (h (f (g x)) 0) 0)))
(assert (= (h (f (g 1)) 0) 1))

(check-sat)
(get-proof)