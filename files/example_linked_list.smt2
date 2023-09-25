; INCLUDE_IN_Z3_BENCHMARK_TEST TRUE
; INCLUDE_IN_VAMPIRE_BENCHMARK_TEST TRUE

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-sort list_element)
(declare-fun next (list_element) list_element)
(declare-fun prev (list_element) list_element)
(declare-const first list_element)
(declare-const last list_element)

(assert (forall ((x0 list_element)) (= (next (prev x0)) x0)))
(assert (forall ((x1 list_element) (x2 list_element)) (=> (= (next x1) x2)(= (prev x2) x1))))
(assert (forall ((x3 list_element)) (not (= (next last) x3))))

(check-sat)
(get-proof)