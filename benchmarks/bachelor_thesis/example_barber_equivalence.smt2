
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true)         ; enable MBQI
(set-option :produce-proofs true)   ; enable proof production

(declare-sort Man)
(declare-fun isShavedBy (Man) Man)
(declare-const barber Man)

; The barber is the "one who shaves all those, and those only, who do not shave themselves". 
(assert (forall ((x Man)) (= (not (= (isShavedBy x) x)) (= (isShavedBy x) barber))))

(check-sat)
(get-proof)