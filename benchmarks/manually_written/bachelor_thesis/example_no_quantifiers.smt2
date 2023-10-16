
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-const x0 Int)
(declare-const x1 Int)

(assert (and (<= x0 x1) (> x0 x1)))

(check-sat)
(get-proof)