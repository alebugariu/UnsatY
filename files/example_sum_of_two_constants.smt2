; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-const x Int)
(declare-const y Int)

(assert (> x 0))
(assert (> y 0))
(assert (<= (+ x y) 0))

(check-sat)
(get-proof)