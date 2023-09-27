; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-fun f (Int) Int)
(declare-fun g (Bool) Bool)
(declare-fun h (Int Bool) Int)

(assert (forall ((x0 Bool)) (g x0)))
(assert (forall ((x1 Bool) (x2 Int)) (=> (not (g x1)) (>= (h x2 x1) x2))))
(assert (forall ((x3 Int)) (=> (> x3 -1) (> (f x3) 7))))
(assert (forall ((x4 Int)) (=> (< x4 1) (= (f x4) 6))))
(assert (forall ((x5 Int) (x6 Bool)) (=> (g x6) (< (h x5 x6) x5))))
(assert (forall ((x7 Bool) (x8 Int) (x9 Int)) (=> (= (f x8) x9) (g x7))))

(check-sat)
(get-proof)

; Possibilities for Representation Format:

; Instantiating the quantified variables x3 = 0, x4 = 0 leads to a contradiction.

; The following assertions set contradictory constraints for x3 = 0, x4 = 0:
; (assert (forall ((x3 Int)) (=> (> x3 -1) (> (f x3) 7))))
; (assert (forall ((x4 Int)) (=> (< x4 1) (= (f x4) 6))))

; The solver cannot find an interpretation for f(0) due to contradictory constraints.

; The uninterpreted function (f (Int) Int) cannot be interpreted due to contradictory constraints for (f 0).

; The uninterpreted function f: Int -> Int cannot be interpreted due to contradictory constraints for f(0).

; Instantiating the quantified variables x3 = 0, x4 = 0 leads to the following contradiction:
; (=> (> 0 -1) (> (f 0) 7))
; (=> (< 0 1) (= (f 0) 6))

; Instantiating the quantified variables x3 = 0, x4 = 0 leads to the following contradiction:
; 0 > -1 => f(0) > 7
; 0 < 1 => f(0) = 6

; Your assertions require both f(0) = 6 and f(0) > 7, which is a contradiction.

; f(0).

; x3 = 0, x4 = 0.