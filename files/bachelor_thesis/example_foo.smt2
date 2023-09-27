
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun foo (Int) Bool)

(assert (forall ((x Int)) (!
  (implies
    (and (< 0 x) (< x 100))
    (foo x))
  :pattern ((foo x))
)))

(assert (not (foo 10)))

(check-sat)
(get-proof)