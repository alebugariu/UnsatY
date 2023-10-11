
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (< x 0))
(assert (< y 0))
(assert (< z 0))
(assert (>= (+ (+ x y) z) 0))

(check-sat)
(get-proof)