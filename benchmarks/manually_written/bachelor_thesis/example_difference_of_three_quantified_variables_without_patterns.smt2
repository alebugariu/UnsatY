
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-const a Int)
(declare-fun f (Int Int Int) Bool)

(assert (forall ((x0 Int) (x1 Int) (x2 Int)) (< (- (- x0 x1) x2) 13)))
(assert (= a 42))

(check-sat-using smt)
(get-proof)