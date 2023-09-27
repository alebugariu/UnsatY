
(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-sort T@U 0)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-sort T@T 0)
(declare-fun type (T@U) T@T)
(declare-fun |Seq@sharp@Empty| (T@T) T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun SeqTypeInv0 (T@T) T@T)
(declare-fun |Seq@sharp@Build| (T@U Int T@U Int) T@U)
(declare-fun |Seq@sharp@Length| (T@U) Int)
(assert (! (forall ((arg016py0 T@T)) (! (= (SeqTypeInv0 (SeqType arg016py0)) arg016py0) :pattern ((SeqType arg016py0)) )) :named O2))
(assert (! (forall ((T5py0 T@T)) (! (= (type (Seq@sharp@Empty T5py0)) (SeqType T5py0)) :pattern ((Seq@sharp@Empty T5py0)) )) :named O3))
(assert (! (forall ((arg018py0 T@U)(arg18py0 Int)(arg20py0 T@U)(arg3py0 Int)) (! (= (type (Seq@sharp@Build arg018py0 arg18py0 arg20py0 arg3py0)) (SeqType (type arg20py0))) :pattern ((Seq@sharp@Build arg018py0 arg18py0 arg20py0 arg3py0)) )) :named O4))
(assert (! (forall ((spy0 T@U)) (! (or (not (= (type spy0) (SeqType (SeqTypeInv0 (type spy0))))) (<= 0 (Seq@sharp@Length spy0))) :pattern ((Seq@sharp@Length spy0)) )) :named O5))
(assert (! (forall ((s1py0 T@U)(ipy0 Int)(vpy0 T@U)(lenpy0 Int)) (! (or (not (= (type s1py0) (SeqType (type vpy0)))) (= (Seq@sharp@Length (Seq@sharp@Build s1py0 ipy0 vpy0 lenpy0)) lenpy0)) :pattern ((Seq@sharp@Length (Seq@sharp@Build s1py0 ipy0 vpy0 lenpy0))) )) :named A1))

;(declare-fun __dummy__ (Int) Bool)
;(declare-const u T@U)

;(assert (! (__dummy__ (Seq@sharp@Length (Seq@sharp@Build (Seq@sharp@Empty (type u)) 0 u -1))) :named Repro))

(check-sat)
(get-info :reason-unknown)
;z3 -T:600 smt-inputs/real-world/pattern_augmenter/ematching/tmp/dafny-seq-a1_1_std_unique_aug-gt_unsat-full.smt2
;unknown
;((:reason-unknown "smt tactic failed to show goal to be sat/unsat (incomplete quantifiers)"))
