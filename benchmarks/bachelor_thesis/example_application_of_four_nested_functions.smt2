
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int Int) Int)
(declare-fun fourth_fun (Bool) Bool)

(assert (forall ((x Int)) (fourth_fun (= (h (f (g x)) 0) 0))))
(assert (= (fourth_fun false) false))
(assert (not (= (h (f (g 5)) 0) 0)))

(check-sat)
(get-proof)