; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :AUTO_CONFIG false)
(set-option :smt.MBQI false)

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (! (forall ((x0 Int)) (! (> (f x0) (f (- x0 1))) :pattern ( (g x0)))) :named A0))
(assert (! (= (f 0) 1) :named A1))
(assert (! (= (f 2) 0) :named A2))

;(assert (! (forall ((x0 Int)) (! (> (f x0) (f (- x0 1))) :pattern ( (g x0)))) :named copy_A0))

;(declare-fun __dummy__ (Int Int) Bool)
;(assert (__dummy__ (g 1) (g 2)))

(check-sat)
(get-proof)

;Solved by: Optset(max_axiom_frequency=2)