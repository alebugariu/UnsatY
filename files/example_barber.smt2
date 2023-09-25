; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-sort man)
(declare-fun shave (man) man)
(declare-const barber man)

; The barber is the "one who shaves all those, and those only, who do not shave themselves". 
(assert (forall ((x0 man)) (=> (not (= (shave x0) x0)) (= (shave x0) barber))))
(assert (forall ((x1 man)) (=> (= (shave x1) barber) (not (= (shave x1) x1)))))

(check-sat)
(get-proof)