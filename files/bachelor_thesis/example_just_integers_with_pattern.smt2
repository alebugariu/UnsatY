; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int Int) Int)
(assert (! (forall ((x0 Int) (y0 Int)) (! (= (+ x0 y0) 3) :pattern ( (f x0 y0)))) :named A0))

(check-sat)
(get-proof)