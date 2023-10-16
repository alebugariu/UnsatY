(set-option :smt.auto-config false)
(set-option :smt.mbqi false)
(set-option :sat.random_seed 488)
(set-option :smt.random_seed 599)
(set-option :nlsat.seed 611)
(set-option :memory_max_size 6000)
(declare-sort |T@U| 0)
(declare-sort RegExStr 0)
(declare-sort RMode 0)
(declare-sort |T@T| 0)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun intType () T@T)
(declare-fun boolType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun type (T@U) T@T)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun MapSelect (T@U T@U) T@U)
(declare-fun MapType (T@T T@T) T@T)
(declare-fun MapKeyType (T@T) T@T)
(declare-fun MapValueType (T@T) T@T)
(declare-fun |Map@sharp@Elements| (T@U) T@U)
(declare-fun |Map@sharp@Domain| (T@U) T@U)
(declare-fun |Set@sharp@Card| (T@U) Int)
(declare-fun |Set@sharp@UnionOne| (T@U T@U) T@U)
(declare-fun |Map@sharp@Card| (T@U) Int)
(declare-fun |Map@sharp@Values| (T@U) T@U)
(declare-fun |Map@sharp@Empty| (T@T T@T) T@U)
(declare-fun |Map@sharp@Build| (T@U T@U T@U) T@U)
(declare-fun u@@5!0 (T@U T@U) T@U)
(declare-fun x@@39!1 (T@U) T@U)
(assert (! (forall ((arg0py0py0 Int)) (! (= (U_2_int (int_2_U arg0py0py0)) arg0py0py0) :pattern ((int_2_U arg0py0py0)) )) :named A0))
(assert (! (forall ((arg0@@0py0py0 Int)) (! (= (type (int_2_U arg0@@0py0py0)) intType) :pattern ((int_2_U arg0@@0py0py0)) )) :named A1))
(assert (! (forall ((arg0@@34py0py0 T@T)(arg1@@7py0py0 T@T)) (! (= (MapKeyType (MapType arg0@@34py0py0 arg1@@7py0py0)) arg0@@34py0py0) :pattern ((MapType arg0@@34py0py0 arg1@@7py0py0)) )) :named A2))
(assert (! (forall ((arg0@@35py0py0 T@T)(arg1@@8py0py0 T@T)) (! (= (MapValueType (MapType arg0@@35py0py0 arg1@@8py0py0)) arg1@@8py0py0) :pattern ((MapType arg0@@35py0py0 arg1@@8py0py0)) )) :named A3))
(assert (! (forall ((m@@9py0py0 T@U)) (! (or (not (= (type m@@9py0py0) (MapType (MapKeyType (type m@@9py0py0)) (MapValueType (type m@@9py0py0))))) (= (Set@sharp@Card (Map@sharp@Values m@@9py0py0)) (Map@sharp@Card m@@9py0py0))) :pattern ((Set@sharp@Card (Map@sharp@Values m@@9py0py0))) )) :named A4))
(assert (! (forall ((m@@10py0py0 T@U)(v@@36py0py0 T@U)) (! (or (not (= (type m@@10py0py0) (MapType (MapKeyType (type m@@10py0py0)) (type v@@36py0py0)))) (and (or (not (U_2_bool (MapSelect (Map@sharp@Values m@@10py0py0) v@@36py0py0))) (and (= (type (u@@5!0 v@@36py0py0 m@@10py0py0)) (MapKeyType (type m@@10py0py0))) (U_2_bool (MapSelect (Map@sharp@Domain m@@10py0py0) (u@@5!0 v@@36py0py0 m@@10py0py0))) (= v@@36py0py0 (MapSelect (Map@sharp@Elements m@@10py0py0) (u@@5!0 v@@36py0py0 m@@10py0py0))))) (or (U_2_bool (MapSelect (Map@sharp@Values m@@10py0py0) v@@36py0py0)) (forall ((u@@6py0py0 T@U)) (! (or (not (= (type u@@6py0py0) (MapKeyType (type m@@10py0py0)))) (not (U_2_bool (MapSelect (Map@sharp@Domain m@@10py0py0) u@@6py0py0))) (not (= v@@36py0py0 (MapSelect (Map@sharp@Elements m@@10py0py0) u@@6py0py0)))) :pattern ((MapSelect (Map@sharp@Domain m@@10py0py0) u@@6py0py0)) :pattern ((MapSelect (Map@sharp@Elements m@@10py0py0) u@@6py0py0)) ))))) :pattern ((MapSelect (Map@sharp@Values m@@10py0py0) v@@36py0py0)) )) :named A5))
(assert (! (forall ((U@@8py0py0 T@T)(V@@7py0py0 T@T)) (! (= (type (Map@sharp@Empty U@@8py0py0 V@@7py0py0)) (MapType U@@8py0py0 V@@7py0py0)) :pattern ((Map@sharp@Empty U@@8py0py0 V@@7py0py0)) )) :named A6))
(assert (! (forall ((u@@7py0py0 T@U)(V@@8py0py0 T@T)) (! (not (U_2_bool (MapSelect (Map@sharp@Domain (Map@sharp@Empty (type u@@7py0py0) V@@8py0py0)) u@@7py0py0))) :pattern ((MapSelect (Map@sharp@Domain (Map@sharp@Empty (type u@@7py0py0) V@@8py0py0)) u@@7py0py0)) )) :named A7))
(assert (! (forall ((m@@13py0py0 T@U)) (! (or (not (= (type m@@13py0py0) (MapType (MapKeyType (type m@@13py0py0)) (MapValueType (type m@@13py0py0))))) (and (or (not (= (Map@sharp@Card m@@13py0py0) 0)) (= m@@13py0py0 (Map@sharp@Empty (MapKeyType (type m@@13py0py0)) (MapValueType (type m@@13py0py0))))) (or (not (= m@@13py0py0 (Map@sharp@Empty (MapKeyType (type m@@13py0py0)) (MapValueType (type m@@13py0py0))))) (= (Map@sharp@Card m@@13py0py0) 0)) (or (= (Map@sharp@Card m@@13py0py0) 0) (and (= (type (x@@39!1 m@@13py0py0)) (MapKeyType (type m@@13py0py0))) (U_2_bool (MapSelect (Map@sharp@Domain m@@13py0py0) (x@@39!1 m@@13py0py0))))))) :pattern ((Map@sharp@Card m@@13py0py0)) )) :named A8))
(assert (! (forall ((arg0@@90py0py0 T@U)(arg1@@38py0py0 T@U)(arg2@@4py0py0 T@U)) (! (= (type (Map@sharp@Build arg0@@90py0py0 arg1@@38py0py0 arg2@@4py0py0)) (MapType (type arg1@@38py0py0) (type arg2@@4py0py0))) :pattern ((Map@sharp@Build arg0@@90py0py0 arg1@@38py0py0 arg2@@4py0py0)) )) :named A9))
(assert (! (forall ((m@@14py0py0 T@U)(u@@8py0py0 T@U)(upy0py0 T@U)(v@@37py0py0 T@U)) (! (or (not (= (type m@@14py0py0) (MapType (type u@@8py0py0) (type v@@37py0py0)))) (not (= (type upy0py0) (type u@@8py0py0))) (and (or (not (= upy0py0 u@@8py0py0)) (and (U_2_bool (MapSelect (Map@sharp@Domain (Map@sharp@Build m@@14py0py0 u@@8py0py0 v@@37py0py0)) upy0py0)) (= (MapSelect (Map@sharp@Elements (Map@sharp@Build m@@14py0py0 u@@8py0py0 v@@37py0py0)) upy0py0) v@@37py0py0))) (or (= upy0py0 u@@8py0py0) (and (or (U_2_bool (MapSelect (Map@sharp@Domain m@@14py0py0) upy0py0)) (not (U_2_bool (MapSelect (Map@sharp@Domain (Map@sharp@Build m@@14py0py0 u@@8py0py0 v@@37py0py0)) upy0py0)))) (or (U_2_bool (MapSelect (Map@sharp@Domain (Map@sharp@Build m@@14py0py0 u@@8py0py0 v@@37py0py0)) upy0py0)) (not (U_2_bool (MapSelect (Map@sharp@Domain m@@14py0py0) upy0py0)))) (= (MapSelect (Map@sharp@Elements (Map@sharp@Build m@@14py0py0 u@@8py0py0 v@@37py0py0)) upy0py0) (MapSelect (Map@sharp@Elements m@@14py0py0) upy0py0)))))) :pattern ((MapSelect (Map@sharp@Domain (Map@sharp@Build m@@14py0py0 u@@8py0py0 v@@37py0py0)) upy0py0)) :pattern ((MapSelect (Map@sharp@Elements (Map@sharp@Build m@@14py0py0 u@@8py0py0 v@@37py0py0)) upy0py0)) )) :named A10))
(assert (! (forall ((m@@16py0py0 T@U)(u@@10py0py0 T@U)(v@@39py0py0 T@U)) (! (or (U_2_bool (MapSelect (Map@sharp@Domain m@@16py0py0) u@@10py0py0)) (not (= (type m@@16py0py0) (MapType (type u@@10py0py0) (type v@@39py0py0)))) (= (Map@sharp@Card (Map@sharp@Build m@@16py0py0 u@@10py0py0 v@@39py0py0)) (+ 1 (Map@sharp@Card m@@16py0py0)))) :pattern ((Map@sharp@Card (Map@sharp@Build m@@16py0py0 u@@10py0py0 v@@39py0py0))) )) :named A11))
(assert (! (forall ((m@@17py0py0 T@U)(u@@11py0py0 T@U)(v@@40py0py0 T@U)) (! (or (not (= (type m@@17py0py0) (MapType (type u@@11py0py0) (type v@@40py0py0)))) (= (Map@sharp@Values (Map@sharp@Build m@@17py0py0 u@@11py0py0 v@@40py0py0)) (Set@sharp@UnionOne (Map@sharp@Values m@@17py0py0) v@@40py0py0))) :pattern ((Map@sharp@Values (Map@sharp@Build m@@17py0py0 u@@11py0py0 v@@40py0py0))) )) :named A12))
(assert (! (forall ((arg0@@63py0py0 T@U)(arg1@@19py0py0 T@U)) (! (= (type (Set@sharp@UnionOne arg0@@63py0py0 arg1@@19py0py0)) (MapType0Type (type arg1@@19py0py0) boolType)) :pattern ((Set@sharp@UnionOne arg0@@63py0py0 arg1@@19py0py0)) )) :named A13))
(assert (! (forall ((a@@4py0py0 T@U)(x@@20py0py0 T@U)) (! (or (= (Set@sharp@Card (Set@sharp@UnionOne a@@4py0py0 x@@20py0py0)) (Set@sharp@Card a@@4py0py0)) (not (= (type a@@4py0py0) (MapType0Type (type x@@20py0py0) boolType))) (not (U_2_bool (MapSelect a@@4py0py0 x@@20py0py0)))) :pattern ((Set@sharp@Card (Set@sharp@UnionOne a@@4py0py0 x@@20py0py0))) )) :named A14))
(check-sat)
(get-info :reason-unknown)
