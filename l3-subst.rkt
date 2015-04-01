#lang racket

(require redex "l3-lang.rkt" "l3-subst-type.rkt")

(provide FV FLV subst substp alpha-eq?)

;; -----------------------------------------------------------------------------
;; Auxiliary functions
;; -----------------------------------------------------------------------------

(define (member? u lst)
  (not (equal? (member u lst) #f)))

;; -----------------------------------------------------------------------------
;; Regular Variables
;; -----------------------------------------------------------------------------

(define-metafunction L3
  FV-value : (X ...) v -> (X ...)
  [(FV-value (X_env ...) *) ()] 
  [(FV-value (X_env ...) n) ()]
  [(FV-value (X_env ...) (v_1 / v_2)) 
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV-value (X_env ...) v_1))
   (where (X_fv2 ...) (FV-value (X_env ...) v_2))]
  [(FV-value (X_env ...) (λ (X T) e))
   (FV-value (X X_env ...) e)]
  [(FV-value (X_env ...) (! v)) 
   (FV-value (X_env ...) v)]
  [(FV-value (X_env ...) (ptr L)) ()]
  [(FV-value (X_env ...) (cap)) ()]
  [(FV-value (X_env ...) (Λ P e)) 
   (FV-value (X_env ...) e)]
  [(FV-value (X_env ...) (loc // v)) 
   (FV-value (X_env ...) v)]
  [(FV-value (X_env1 ... X_term X_env2 ...) X_term) ()]
  [(FV-value (X_env ...) X_term) (X_term)]
  [(FV-value (X_env ...) (inl v as T)) 
   (FV-value (X_env ...) v)]
  [(FV-value (X_env ...) (inr v as T)) 
   (FV-value (X_env ...) v)])


;;auxiliary function for FV
(define-metafunction L3
  FV-acc : (X ...) e -> (X ...)
  [(FV-acc (X ...) *) ()]
  [(FV-acc (X ...) n) ()]
  [(FV-acc (X ...) (let * = e_1 in e_2))
   (X_fv1 ... X_fv2 ...) 
   (where (X_fv1 ...) (FV-acc (X ...) e_1))
   (where (X_fv2 ...) (FV-acc (X ...) e_2))]  
  [(FV-acc (X ...) (e_1 / e_2))
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV-acc (X ...) e_1))
   (where (X_fv2 ...) (FV-acc (X ...) e_2))]
  [(FV-acc (X ...) (let (X_1 / X_2) = e_1 in e_2))
   (X_fv1 ... X_fv2 ...) 
   (where (X_fv1 ...) (FV-acc (X ...) e_1))
   (where (X_fv2 ...) (FV-acc (X_1 X_2 X ...) e_2))]
  ; variable that is bound in environment
  [(FV-acc (X_env1 ... X_term X_env2 ...) X_term) ()]
  ; variable that is not bound in environment
  [(FV-acc (X_env ...) X_term) (X_term)]
  [(FV-acc (X_env ...) (λ (X T) e)) (FV-acc (X X_env ...) e)]
  [(FV-acc (X ...) (e_1 e_2)) 
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV-acc (X ...) e_1))
   (where (X_fv2 ...) (FV-acc (X ...) e_2))]
  [(FV-acc (X_env ...) (! v))
   (FV-value (X_env ...) v)]
  [(FV-acc (X_env ...) (let (! X) = e_1 in e_2))
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV-acc (X_env ...) e_1))
   (where (X_fv2 ...) (FV-acc (X X_env ...) e_2))]
  [(FV-acc (X ...) (dupl e)) (FV-acc (X ...) e)]
  [(FV-acc (X ...) (drop e)) (FV-acc (X ...) e)]
  [(FV-acc (X ...) (ptr L)) ()]
  [(FV-acc (X ...) cap) ()]
  [(FV-acc (X ...) (new e)) (FV-acc (X ...) e)] 
  [(FV-acc (X ...) (free e)) (FV-acc (X ...) e)]
  [(FV-acc (X ...) (swap e_1 e_2 e_3))
   (X_fv1 ... X_fv2 ... X_fv3 ...)
   (where (X_fv1 ...) (FV-acc (X ...) e_1))
   (where (X_fv2 ...) (FV-acc (X ...) e_2))
   (where (X_fv3 ...) (FV-acc (X ...) e_3))]
  [(FV-acc (X ...) (Λ p e)) (FV-acc (X ...) e)]
  [(FV-acc (X ...) (e loc)) (FV-acc (X ...) e)]
  [(FV-acc (X ...) (loc // e)) (FV-acc (X ...) e)]
  [(FV-acc (X_env ...) (let (loc // X) = e_1 in e_2))
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV-acc (X_env ...) e_1))
   (where (X_fv2 ...) (FV-acc (X X_env ...) e_2))]
  [(FV-acc (X_fv1 ...) (inl e as T))
   (FV-acc (X_fv1 ...) e)]
  [(FV-acc (X_fv1 ...) (inr e as T))
   (FV-acc (X_fv1 ...) e)]
  [(FV-acc (X_env ...) (case e_c of (inl X) => e_l \| (inr X) => e_r))
   (X_envc ... X_envl ... X_envr ...)
   (where (X_envc ...) (FV-acc (X X_env ...) e_c))
   (where (X_envl ...) (FV-acc (X X_env ...) e_l))
   (where (X_envr ...) (FV-acc (X X_env ...) e_r))])



; returns list (from left to right) of all free variables of input expression
(define-metafunction L3
  FV : e -> (X ...)
  [(FV e) 
   ,(remove-duplicates (term (FV-acc () e)))])



(define-metafunction L3
  ;substitute v for all occurences of X in e_1
  subst : e_1 X v -> e
  [(subst * X v) *]
  [(subst n X v) n]
  [(subst (let * = e_11 in e_12) X v)
   (let * = (subst e_11 X v) in (subst e_12 X v))]
  [(subst (e_11 / e_12) X v) ((subst e_11 X v) / (subst e_12 X v))]
  
  ;; case let-pair1: subst on one of the bounded variables. 
  ;; only subst on e_1. No effect on e_2. 
  [(subst (let (X / X_2) = e_1 in e_2) X v) 
   (let (X / X_2) = (subst e_1 X v) in e_2)]
  [(subst (let (X_1 / X) = e_1 in e_2) X v) 
   (let (X_1 / X) = (subst e_1 X v) in e_2)]  
  ;; case let-pair2: Different variables, none ∈ FV(v).
  [(subst (let (X_1 / X_2) = e_1 in e_2) X v) 
   (let (X_1 / X_2) = (subst e_1 X v) in (subst e_2 X v))
   (where (X_free ...) (FV v))
   (side-condition (and (not (member? (term X_1) (term (X_free ...))))
                        (not (member? (term X_2) (term (X_free ...))))))]
  ;; case let-pair3: X_1 or X_2 in FV(v), have to rename. We need several cases
  ;; in order to make it more efficient, e.g. avoid two renamings when only one
  ;; of the variables ∈ FV(v) 
  ;; case X_1 ∈ FV(v), X_2 not ∈ FV(v). Just rename X_1
  [(subst (let (X_1 / X_2) = e_1 in e_2) X v)
   (let (X_1fresh / X_2) = (subst e_1 X v) in 
     (subst (subst e_2 X_1 X_1fresh) X v))
   (where (X_freev ...) (FV v))
   (where X_1fresh 
          ,(variable-not-in 
            (term ((FV e_2) (FV v) X)) 
            (term X_1)))
   (side-condition (not (member? (term X_2) (term (X_freev ...)))))]
  ;; case X_1 not ∈ FV(v), X_2 ∈ FV(v). Just rename X_2
   [(subst (let (X_1 / X_2) = e_1 in e_2) X v)
   (let (X_1 / X_2fresh) = (subst e_1 X v) in 
     (subst (subst e_2 X_2 X_2fresh) X v))
   (where (X_freev ...) (FV v))
   (where X_2fresh 
          ,(variable-not-in 
            (term ((FV e_2) (FV v) X)) 
            (term X_2)))
   (side-condition (not (member? (term X_1) (term (X_freev ...)))))] 
  ;; case X_1 ∈ FV(v), X_2 ∈ FV(v). Rename both X_1 and X_2   
  [(subst (let (X_1 / X_2) = e_1 in e_2) X v)
   (let (X_1fresh / X_2fresh) = (subst e_1 X v) in 
     (subst (subst (subst e_2 X_1 X_1fresh) X_2 X_2fresh) X v))
   ;;This is to avoid to recalculate FV, which might be expensive
   (where (X_free_e1 ...) (FV e_1))
   (where (X_free_e2 ...) (FV e_2))
   (where (X_free_v ...) (FV v))  
   (where X_1fresh 
          ,(variable-not-in 
            (term ((X_free_e2 ...) (X_free_v ...) X)) 
            (term X_1)))
   (where X_2fresh 
          ,(variable-not-in 
            (term ((X_free_e2 ...) (X_free_v ...) X X_1fresh)) 
            (term X_2)))]
  [(subst X X v) v]
  [(subst X_1 X v) X_1]  
  ;; Possible variable capture cases
  ;; case λ1: subst on bounded variable. No effect.
  [(subst (λ (X T) e) X v) (λ (X T) e)] 
  ;; case λ2: X_0 not in FV(v), no capture risk.   
  [(subst (λ (X_0 T) e) X_1 v) 
   (λ (X_0 T) (subst e X_1 v))
   (side-condition (not(member? (term X_0) (term (FV v)))))] 
  ;; case λ3: X_0 in FV(v), have to rename.
  [(subst (λ (X_0 T) e) X_1 v)
   (λ (X_fresh T) (subst (subst e X_0 X_fresh) X_1 v))
   (where X_fresh ,(variable-not-in 
                     (term ((FV e) (FV v) X_1)) 
                     (term X_0)))]
  [(subst (e_11 e_12) X v) 
   ((subst e_11 X v) (subst e_12 X v))]
  [(subst (! v_1) X v) (! (subst v_1 X v))]
  
  ;; case !1: subst on bounded variable. No effect on e_2.
  [(subst (let (! X) = e_1 in e_2) X v) 
   (let (! X) = (subst e_1 X v) in e_2)]
  ;; case !2: X_0 not in FV(v), no capture risk. 
  [(subst (let (! X_0) = e_1 in e_2) X v) 
   (let (! X_0) = (subst e_1 X v) in (subst e_2 X v))
   (side-condition (not (member? (term X_0) (term (FV v)))))]
  ;; case !3: X_0 in FV(v), have to rename.
  [(subst (let (! X_0) = e_1 in e_2) X v)
   (let (! X_1fresh) = (subst e_1 X v) in 
     (subst (subst e_2 X_0 X_1fresh) X v))
   (where X_1fresh ,(variable-not-in 
                     (term ((FV v) (FV e_2) X)) 
                     (term X_0)))]

[(subst (dupl e) X v) (dupl (subst e X v))]
  [(subst (drop e) X v) (drop (subst e X v))]
  [(subst (ptr L) X v) (ptr L)]
  [(subst cap X v) cap]
  [(subst (new e) X v) (new (subst e X v))]
  [(subst (free e) X v) (free (subst e X v))]
  [(subst (swap e_1 e_2 e_3) X v) 
   (swap (subst e_1 X v) (subst e_2 X v) (subst e_3 X v))]
  [(subst (Λ P e) X v) 
   (Λ P_fresh (subst (substp e P P_fresh) X v))
   (where P_fresh ,(variable-not-in 
                    (term ((FLV e) (FLV v))) 
                    (term P)))]
  [(subst (e loc) X v) ((subst e X v) loc)]
  [(subst (loc // e) X v) (loc // (subst e X v))]
  ;; let acts as a binder for P and X. X shouldn't be replaced inside of e_2.
  ;; only change e_1. Why change P? we are only replacing regular vars, not loc
  ;; vars.
 ; [(subst (let (P // X) = e_1 in e_2) X v)
 ;  (let (P_prime // X) = (subst e_1 X v) in (subst (substp e_2 P P_prime) X v))
 ;  (where P_prime ,(variable-not-in (term ((FLV e_2) (FLV v)))))]
  [(subst (let (P // X) = e_1 in e_2) X v)
   (let (P // X) = (subst e_1 X v) in e_2)]
  ;; If binded X is different from what we want to substitute.
  ;; Possible variable capture in e_2 (if X_new ∈ (FV e_2) and v = X)                
  [(subst (let (P // X_curr) = e_1 in e_2) X_new v) 
   (let (P // X_curr) = (subst e_1 X_new v) in (subst e_2 X_new v))]
  [(subst (inl e as T) X v)
   (inl (subst e X v) as T)]
  [(subst (inr e as T) X v)
   (inr (subst e X v) as T)]
  ;; case case-1: subst on bounded variable. No effect on e_l or e_r.
  [(subst (case e_c of (inl X) => e_l \| (inr X) => e_r) X v)
   (case (subst e_c X v) of (inl X) => e_l \| (inr X) => e_r)]
  ;; case case-2: Bounded X is not in FV(v), no capture risk.
  [(subst (case e_c of (inl X_b) => e_l \| (inr X_b) => e_r) X v)
   (case (subst e_c X v) of 
     (inl X_b) => (subst e_l X v) \| 
     (inr X_b) => (subst e_r X v))
   (side-condition (not (member? (term X_b) (term (FV v)))))]
  ;; case case-3: Bounded X in FV(v), have to rename.
  [(subst (case e_c of (inl X_b) => e_l \| (inr X_b) => e_r) X v)
   (case (subst e_c X v) of 
     (inl X_fresh) => (subst (subst e_l X_b X_fresh) X v) \| 
     (inr X_fresh) => (subst (subst e_r X_b X_fresh) X v))
   (where X_fresh ,(variable-not-in 
                    (term ((FV e_l) (FV e_r) (FV v))) 
                    (term X_b)))])


(define-judgment-form L3
  #:mode (alpha-eq? I I)
  #:contract (alpha-eq? e e)
  
  [--------------------------------------------------------------
   (alpha-eq? * *)]

  [(alpha-eq? e_11 e_21)
   (alpha-eq? e_12 e_22)
   --------------------------------------------------------------
   (alpha-eq? (let * = e_11 in e_12) 
              (let * = e_21 in e_22))]

  [(alpha-eq? e_11 e_21)
   (alpha-eq? e_12 e_22)
   --------------------------------------------------------------
   (alpha-eq? (e_11 / e_12) 
              (e_21 / e_22))]

  [(where X_31 ,(variable-not-in 
                 (term ((FreeVars e_12) (FreeVars e_22))) 
                 (term X_11)))
   (where X_32 ,(variable-not-in 
                 (term ((FreeVars e_12) (FreeVars e_22))) 
                 (term X_12)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst (subst e_12 X_11 X_31) X_12 X_32) 
                     (subst (subst e_22 X_21 X_31) X_22 X_32))
   --------------------------------------------------------------
   (alpha-eq? (let (X_11 / X_12) = e_11 in e_12) 
              (let (X_21 / X_22) = e_21 in e_22))]

  [--------------------------------------------------------------
   (alpha-eq? X X)]

  [(where X_3 ,(variable-not-in 
                (term ((FreeVars e_1) (FreeVars e_2))) 
                (term X_1)))
   (alpha-eq? (subst e_1 X_1 X_3) (subst e_2 X_2 X_3))
   (side-condition (alpha-eq-T? T_1 T_2))
   --------------------------------------------------------------
   (alpha-eq? (λ (X_1 T_1) e_1) 
              (λ (X_2 T_2) e_2))]

  [(alpha-eq? e_11 e_21) 
   (alpha-eq? e_12 e_22)
   --------------------------------------------------------------
   (alpha-eq? (e_11 e_12) (e_21 e_22))]
  
  [(alpha-eq? v_1 v_2)
   --------------------------------------------------------------
   (alpha-eq? (! v_1) (! v_2))]
  
  [(where X_3 ,(variable-not-in 
                (term ((FreeVars e_12) (FreeVars e_22))) 
                (term X_1)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst e_12 X_1 X_3) (subst e_22 X_2 X_3))
   --------------------------------------------------------------
   (alpha-eq? (let (! X_1) = e_11 in e_12) 
              (let (! X_2) = e_21 in e_22))]

  [(alpha-eq? e_1 e_2)
   --------------------------------------------------------------
   (alpha-eq? (dupl e_1) (dupl e_2))]
  
  [(alpha-eq? e_1 e_2)
   --------------------------------------------------------------
   (alpha-eq? (drop e_1) (drop e_2))]

  [--------------------------------------------------------------
   (alpha-eq? (ptr L) (ptr L))]
  
  [--------------------------------------------------------------
   (alpha-eq? cap cap)]
  
  [(alpha-eq? e_1 e_2)
   --------------------------------------------------------------
   (alpha-eq? (new e_1) (new e_2))]
  
  [(alpha-eq? e_1 e_2)
   --------------------------------------------------------------
   (alpha-eq? (free e_1) (free e_2))]
  
  [(alpha-eq? e_11 e_21)
   (alpha-eq? e_12 e_22)
   (alpha-eq? e_13 e_23)
   --------------------------------------------------------------
   (alpha-eq? (swap e_11 e_12 e_13) 
              (swap e_21 e_22 e_23))]
  
  [(where P_3 ,(variable-not-in 
                (term ((FreeLocs e_1) (FreeLocs e_2))) 
                (term P_1)))
   (alpha-eq? (substp e_1 P_1 P_3) (substp e_2 P_2 P_3))
   --------------------------------------------------------------
   (alpha-eq? (Λ P_1 e_1) (Λ P_2 e_2))]

  [(alpha-eq? e_1 e_2)
   --------------------------------------------------------------
   (alpha-eq? (e_1 loc) (e_2 loc))]

  [(alpha-eq? e_1 e_2)
   --------------------------------------------------------------
   (alpha-eq? (loc // e_1) (loc // e_2))]
  
  [(where X_3 ,(variable-not-in 
                (term ((FreeVars e_12) (FreeVars e_22))) 
                (term X_1)))
   (where P_3 ,(variable-not-in 
                (term ((FreeLocs e_12) (FreeLocs e_22))) 
                (term P_1)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst (substp e_12 P_1 P_3) X_1 X_3) 
              (subst (substp e_22 P_2 P_3) X_2 X_3))
   --------------------------------------------------------------
   (alpha-eq? (let (P_1 // X_1) = e_11 in e_12) 
              (let (P_2 // X_2) = e_21 in e_22))])


(module+ test
  (require rackunit)
  ;FV
  (check-equal? (term (FV (λ (x I) *))) '())
  (check-equal? (term (FV ((λ (x I) z) y))) '(z y))
  (check-equal? (term (FV (let (x / y) = (x z) in (x y)))) '(x z))
  
)


(module+ test
  ;alpha-eq?
  (test-equal 
    (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in y))) #t)
  (test-equal 
    (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in x))) #f)
  (test-equal 
    (judgment-holds (alpha-eq? (let (! x) = (λ (y I) y) in x) 
                               (let (! y) = (λ (z I) z) in y))) #t))









;; -----------------------------------------------------------------------------
;; Location variables
;; -----------------------------------------------------------------------------

(define-metafunction L3
  FLV-value : (P ...) v -> (P ...)
  [(FLV-value (P_env ...) *) ()] 
  [(FLV-value (P_env ...) (v_1 / v_2)) 
   (P_fv1 ... P_fv2 ...)
   (where (P_fv1 ...) (FLV-value (P_env ...) v_1))
   (where (P_fv2 ...) (FLV-value (P_env ...) v_2))]
  [(FLV-value (P_env ...) (λ (X T) e))
   (FLV-value (P_env ...) e)]
  [(FLV-value (P_env ...) (! v)) 
   (FLV-value (P_env ...) v)]
  [(FLV-value (P_env ...) (ptr L)) ()]
  [(FLV-value (P_env ...) (cap)) ()]
  [(FLV-value (P_env ...) (Λ P e)) 
   (FLV-value (P P_env ...) e)]
  [(FLV-value (P_env ...) (P // v)) 
   (FLV-value (P P_env ...) v)]
  [(FLV-value (P_env ...) (L // v)) 
   (FLV-value (P_env ...) v)]
  [(FLV-value (P_env ...) X) ()]
  [(FLV-value (P_env ...) (inl v as T)) 
   (FLV-value (P_env ...) v)]
  [(FLV-value (P_env ...) (inr v as T)) 
   (FLV-value (P_env ...) v)])


(define-metafunction L3
  FLV-acc : (P ...) e -> (P ...)
  [(FLV-acc (P_env ...) *) ()]
  [(FLV-acc (P_env ...) (let * = e_1 in e_2))
   (P_fl1 ... P_fl2 ...) 
   (where (P_fl1 ...) (FLV-acc (P_env ...) e_1))
   (where (P_fl2 ...) (FLV-acc (P_env ...) e_2))]  
  [(FLV-acc (P_env ...) (e_1 / e_2))
   (P_fl1 ... P_fl2 ...) 
   (where (P_fl1 ...) (FLV-acc (P_env ...) e_1))
   (where (P_fl2 ...) (FLV-acc (P_env ...) e_2))]
  [(FLV-acc (P_env ...) (let (X_1 / X_2) = e_1 in e_2))
   (P_fl1 ... P_fl2 ...) 
   (where (P_fl1 ...) (FLV-acc (P_env ...) e_1))
   (where (P_fl2 ...) (FLV-acc (P_env ...) e_2))]
  [(FLV-acc (P_env ...) X) ()]
  ;; This would imply that location variables on types are related to 
  ;; location variable names on expressions, which I don't think is true.
  [(FLV-acc (P_env ...) (λ (X T) e))
   ;(loc_T ... loc_e ...)
   ;(where (loc_T ...) (type-FL (loc ...) T))
   (FLV-acc (P_env ...) e)]
  [(FLV-acc (P_env ...) (e_1 e_2)) 
   (P_fl1 ... P_fl2 ...) 
   (where (P_fl1 ...) (FLV-acc (P_env ...) e_1))
   (where (P_fl2 ...) (FLV-acc (P_env ...) e_2))]
  [(FLV-acc (P_env ...) X) ()]  
  [(FLV-acc (P_env ...) (! v)) (FLV-value (P_env ...) v)]
  [(FLV-acc (P_env ...) (let (! X) = e_1 in e_2))
   (P_fl1 ... P_fl2 ...) 
   (where (P_fl1 ...) (FLV-acc (P_env ...) e_1))
   (where (P_fl2 ...) (FLV-acc (P_env ...) e_2))]
  [(FLV-acc (P_env ...) (dupl e)) (FLV-acc (P_env ...) e)]
  [(FLV-acc (P_env ...) (drop e)) (FLV-acc (P_env ...) e)] 
  [(FLV-acc (P_env ...) (ptr L)) ()]
  [(FLV-acc (P_env ...) cap) ()]
  [(FLV-acc (P_env ...) (new e)) 
   (FLV-acc (P_env ...) e)] 
  [(FLV-acc (P_env ...) (free e)) 
   (FLV-acc (P_env ...) e)]
  [(FLV-acc (P_env ...) (swap e_1 e_2 e_3))
   (P_fl1 ... P_fl2 ... P_fl3 ...)
   (where (P_fl1 ...) (FLV-acc (P_env ...) e_1))
   (where (P_fl2 ...) (FLV-acc (P_env ...) e_2))
   (where (P_fl3 ...) (FLV-acc (P_env ...) e_3))]
  ;; location universal quantifier introduction
  [(FLV-acc (P_env ...) (Λ P e)) 
   (FLV-acc (P P_env ...) e)]
  ;; location universal quantifier elimination 
  ;; Is there any bounding here? 
  [(FLV-acc (P_env ...) (e loc)) 
   (FLV-acc (P_env ...) e)]
  ;; location existential quantifier introduction
  ;; case for pointer variable: Add P to environment and recurse on e
  [(FLV-acc (P_env ...) (P // e)) 
   (FLV-acc (P P_env ...) e)]
  ;; case for pointer constant: Just recursion on e
  [(FLV-acc (P_env ...) (L // e)) 
   (FLV-acc (P_env ...) e)]
  ;; location existential quantifier elimination
  [(FLV-acc (P_env ...) (let (P // X) = e_1 in e_2))
   (P_fl1 ... P_fl2 ...)
   (where (P_fl1 ...) (FLV-acc (P_env ...) e_1))
   (where (P_fl2 ...) (FLV-acc (P P_env ...) e_2))]
  [(FLV-acc (P_env ...) (inl e as T))
   (FLV-acc (P_env ...) e)]
  [(FLV-acc (P_env ...) (inr e as T))
   (FLV-acc (P_env ...) e)]
  [(FLV-acc (P_env ...) (case e_c of (inl X) => e_l \| (inr X) => e_r))
   (P_envc ... P_envl ... P_envr ...)
   (where (P_envc ...) (FLV-acc (P_env ...) e_c))
   (where (P_envl ...) (FLV-acc (P_env ...) e_l))
   (where (P_envr ...) (FLV-acc (P_env ...) e_r))])

(define-metafunction L3
  FLV : e -> (loc ...)
  [(FLV e) (FLV-acc () e)])


; TODO: attach type ascriptions to let bindings?
(define-metafunction L3
  ;substitute loc for p in e_in
  substp : e_in P loc -> e_out
  [(substp * P loc) *]
  [(substp n P loc) n]
  [(substp (let * = e_11 in e_12) P loc)
   (let * = (substp e_11 P loc) in (substp e_12 P loc))]
  [(substp (e_11 / e_12) P loc) ((substp e_11 P loc) / (substp e_12 P loc))]
  [(substp (let (X_1 / X_2) = e_11 in e_12) P loc)
   (let (X_1 / X_2) = (substp e_11 P loc) in (substp e_12 P loc))]
  [(substp X P loc) X]
  [(substp (λ (X T) e_11) P loc) 
   (λ (X (type-substp T P loc)) (substp e_11 P loc))]
  [(substp (e_11 e_12) P loc) ((substp e_11 P loc) (substp e_12 P loc))]
  [(substp (! v) P loc) (! (substp v P loc))]
  [(substp (let (! X) = e_11 in e_12) P loc) 
   (let (! X) = (substp e_11 P loc) in (substp e_12 P loc))]
  [(substp (dupl e) P loc) (dupl (substp e P loc))]
  [(substp (drop e) P loc) (drop (substp e P loc))]
  [(substp (ptr L) P loc) (ptr L)]
  [(substp cap P loc) cap]
  [(substp (new e) P loc) (new (substp e P loc))]
  [(substp (free e) P loc) (free (substp e P loc))]
  [(substp (swap e_1 e_2 e_3) P loc) 
   (swap (substp e_1 P loc) (substp e_2 P loc) (substp e_3 P loc))]
  ;; Possible variable capture cases
  ;; case Λ1: subst on bounded variable. No effect.
  [(substp (Λ P e) P loc) (Λ P e)]
  ;; case Λ2: P_0 not in FLV(loc), no capture risk. Consider two sub-cases:
  ;; 1) loc = location constant. Proceed with substitution
  [(substp (Λ P_0 e) P_1 L) 
   (Λ P_0 (substp e P_1 L))]
  ;; 2) loc = P_new / P-new != P_0. Proceed with substitution.
  [(substp (Λ P_0 e) P_1 P_new) 
   (Λ P_0 (substp e P_1 P_new))
   (side-condition (not (equal? (term P_0) (term P_new))))] 
  ;; case Λ3: P_0 in FLV(loc), have to rename. This is the same as trying to 
  ;; substitute P_1 for P_0.
  [(substp (Λ P_0 e) P_1 P_0)
   (Λ P_2 (substp e_ren P_1 P_0))   
   (where P_2 ,(variable-not-in (term (P_0 e)) (term P_0)))
   (where e_ren (substp e P_0 P_2))]    
  ;; explicit application with a matching variable.
  [(substp (e P) P loc) 
   ((substp e P loc) loc)]  
  ;; explicit application with a constant/non-matching variable.
  [(substp (e loc_1) P loc) 
   ((substp e P loc) loc_1)]
  [(substp (P // e) P loc) (loc // (substp e P loc))]
  [(substp (loc_1 // e) P loc) (loc_1 // (substp e P loc))]
  [(substp (let (P // X) = e_1 in e_2) P loc)
   (let (P // X) = (substp e_1 P loc) in e_2)]
  [(substp (let (P_1 // X) = e_1 in e_2) P loc)
   (let (P_1 // X) = (substp e_1 P loc) in (substp e_2 P loc))]
  [(substp (inl e as T) P loc)
   (inl (substp e P loc) as T)]
  [(substp (inr e as T) P loc)
   (inr (substp e P loc) as T)]
  [(substp (case e_c of (inl X) => e_l \| (inr X) => e_r) P loc)
   (case (substp e_c P loc) of 
     (inl X) => (substp e_l P loc) \| 
     (inr X) => (substp e_r P loc))])




