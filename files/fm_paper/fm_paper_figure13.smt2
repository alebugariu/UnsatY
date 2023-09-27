
(set-option :AUTO_CONFIG false)
(set-option :smt.MBQI false)

(declare-fun P (Int) Bool)
(declare-fun Q (Int Int Int) Bool)
(declare-fun R (Int Int) Bool)
(assert (forall ((a0 Int)) (!
  (or
    (not (P a0))
    (forall ((b0 Int) (c0 Int)) (!
        (Q b0 c0 a0)
     :pattern ((Q b0 c0 a0)) )))
 :pattern ((P a0)))))

(assert (forall ((d0 Int)) (!
  (or
    (not (P d0))
    (forall ((e0 Int) (f0 Int)) (!
        (R e0 d0)
     :pattern ((Q e0 f0 d0)) )))
 :pattern ((P d0)))))

(assert (forall ((z1 Int)) (! (P z1) :pattern ((P z1)))))
(assert (forall ((y2 Int) (z2 Int)) (! (not (R y2 z2)) :pattern ((R y2 z2)))))


;(declare-fun __dummy__ (Bool Bool) Bool)
;(assert (__dummy__ (P 0) (Q 0 0 0)))

(check-sat)
(get-proof)