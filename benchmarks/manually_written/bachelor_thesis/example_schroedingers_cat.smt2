
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-sort cat)
(declare-fun alive (cat) Bool)

(assert (forall ((x0 cat)) (alive x0)))
(assert (forall ((x1 cat)) (not (alive x1))))

(check-sat)
(get-proof)