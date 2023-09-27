
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun len (Int) Int)
(declare-fun nxt (Int) Int)

(assert (forall ((x0 Int)) (> (len(nxt x0)) 0)))
(assert (forall ((x1 Int)) (or (= (nxt x1) x1) (= (len(nxt x1)) (+ (len(nxt x1)) 1)))))
(assert (forall ((x2 Int)) (or (not (= (nxt x2) x2)) (= (len(nxt x2)) 1))))

(assert (<= (len 7) 0))

(check-sat)
(get-proof)