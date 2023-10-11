
(set-option :AUTO_CONFIG false)
(set-option :smt.MBQI false)

(declare-sort T@U 0)
(declare-sort T@T 0)
(declare-fun type (T@U) T@T)
(declare-fun 
    |SeqEmpty| 
    (T@T) T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun SeqElementType (T@T) T@T)
(declare-fun 
    |SeqBuild| 
    (T@U Int T@U Int) T@U)
(declare-fun 
    |SeqLength|
    (T@U) Int)

(assert (! (forall 
    
    ((t0 T@T)) 
    
    (! 
    
        (= (SeqElementType (SeqType t0)) t0) 
        
        :pattern ((SeqType t0))  
    
    )) :named A0))

(assert (! (forall 
    
    ((t1 T@T)) 
    
    (! 
    
        (= (type (|SeqEmpty| t1)) (SeqType t1)) 
        
        :pattern ((|SeqEmpty| t1))  
    
    )) :named A1))

(assert (! (forall 
    
    ((s2 T@U) (i2 Int) (v2 T@U) (len2 Int)) 
    
    (! 
    
        (let ((T7 (type v2))) (= (type (|SeqBuild| s2 i2 v2 len2)) (SeqType T7)))
        
        :pattern ((|SeqBuild| s2 i2 v2 len2))  
    
    )) :named A2))

(assert (! (forall 
    
    ((s3 T@U))
    
    (! 
    
        (let ((T24 (SeqElementType (type s3)))) (or (not (= (type s3) (SeqType T24))) (<= 0 (|SeqLength| s3))))
        
        :pattern ((|SeqLength| s3))
    
    )) :named A3))

(assert (! (forall 
    
    ((s4 T@U) (i4 Int) (v4 T@U) (len4 Int))
    
    (! 
    
        (let ((T27 (type v4))) (or (not (= (type s4) (SeqType T27))) (= (|SeqLength| (|SeqBuild| s4 i4 v4 len4)) len4)))
        
        :pattern ((|SeqLength| (|SeqBuild| s4 i4 v4 len4)))
    
    )) :named A4))


;(declare-fun __dummy__ (Int) Bool)
;(declare-const v T@U)

;(assert (__dummy__ (|SeqLength| (|SeqBuild| (|SeqEmpty| (type v)) 0 v -1))))

;(declare-fun __dummy2__ (Int Int T@T T@U) Bool)
;(declare-const s T@U)
;(declare-const ss T@U)
;(declare-const v T@U)

;(assert (__dummy2__ (|SeqLength| s) (|SeqLength| (|SeqBuild| (|SeqBuild| ss 1 v 2) 3 v -1))
;        (SeqType (type v)) (|SeqEmpty| (type v))))


;(declare-fun __dummy3__ (Int) Bool)
;(declare-const s T@U)
;(declare-const v T@U)

;(assert (__dummy3__ (|SeqLength| (|SeqBuild| (|SeqBuild| s 1 v 2) 3 v -1))))

;(declare-fun __dummy4__ (Int) Bool)
;(declare-const s T@U)
;(declare-const v T@U)

;(assert (__dummy4__ (|SeqLength| (|SeqBuild| (|SeqBuild| s 0 v -1) 0 v -1))))

(check-sat)
(get-proof)