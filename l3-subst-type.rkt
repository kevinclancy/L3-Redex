#lang racket

(require redex "l3-lang.rkt")

(provide type-FLV type-substp type-subst alpha-eq-T?)

(define (member? u lst)
  (not (equal? (member u lst) #f)))



(define-metafunction L3
  type-FLV-acc : (P ...) T -> (P ...)
  [(type-FLV-acc (P ...) I) ()]
  [(type-FLV-acc (P ...) Int) ()]
  [(type-FLV-acc (P ...) tX ) ()]
  [(type-FLV-acc (P ...) (T_1 ⊗ T_2)) 
   (P_FL1 ... P_FL2 ...)
   (where (P_FL1 ...) (type-FLV-acc (P ...) T_1))
   (where (P_FL2 ...) (type-FLV-acc (P ...) T_2))]
  [(type-FLV-acc (P ...) (T_1 + T_2)) 
   (P_FL1 ... P_FL2 ...)
   (where (P_FL1 ...) (type-FLV-acc (P ...) T_1))
   (where (P_FL2 ...) (type-FLV-acc (P ...) T_2))]
  [(type-FLV-acc (P ...) (T_1 -o T_2))
   (P_FL1 ... P_FL2 ...)
   (where (P_FL1 ...) (type-FLV-acc (P ...) T_1))
   (where (P_FL2 ...) (type-FLV-acc (P ...) T_2))]
  [(type-FLV-acc (P ...) (! T)) (type-FLV-acc (P ...) T)]
  ; P appears on env, then it is bounded on a Ptr expression.
  [(type-FLV-acc (P_env1 ... P P_env2 ...) (Ptr P)) ()]
  ; else, P is a free location variable
  [(type-FLV-acc (P_env ...) (Ptr P)) (P)]
  ; case for a Ptr to constant location
  [(type-FLV-acc (P_env ...) (Ptr L)) ()]
  ; P appears on env, then it is bounded on a Cap expression.
  [(type-FLV-acc (P_env1 ... P P_env2 ...) (Cap P T))
   (type-FLV-acc (P_env1 ... P P_env2 ...) T)]
  ; else, P is a free location variable
  [(type-FLV-acc (P_env ...) (Cap P T)) 
   (P P_T ...)
   (where (P_T ...) (type-FLV-acc (P_env ...) T))]
  [(type-FLV-acc (P_env ...) (∀ P T)) (type-FLV-acc (P P_env ...) T)]
  [(type-FLV-acc (P_env ...) (∃ P T)) (type-FLV-acc (P P_env ...) T)]
  [(type-FLV-acc (P_env ...) (μ tX T)) (type-FLV-acc (P_env ...) T)])
  
(define-metafunction L3
  type-FLV : T -> (P ...)
  [(type-FLV T) 
   ,(remove-duplicates (term (type-FLV-acc () T)))])

;location substitution for types
(define-metafunction L3
  type-substp : T_in P loc -> T_out
  [(type-substp I P loc) I]
  [(type-substp Int P loc) Int]
  [(type-substp tX P loc) tX]
  [(type-substp (T_1 ⊗ T_2) P loc) 
   ((type-substp T_1 P loc) ⊗ (type-substp T_2 P loc))]
  [(type-substp (T_1 + T_2) P loc) 
   ((type-substp T_1 P loc) + (type-substp T_2 P loc))]
  [(type-substp (T_1 -o T_2) P loc) 
   ((type-substp T_1 P loc) -o (type-substp T_2 P loc))]
  [(type-substp (! T) P loc) (! (type-substp T P loc))]
  ;; substitution on Ptr type: case variable matches
  [(type-substp (Ptr P) P loc) (Ptr loc)]
  ;; substitution on Ptr type: all other cases (include Ptr to constants and 
  ;; variables.
  [(type-substp (Ptr loc_1) P loc) (Ptr loc_1)]
  ;; substitution on Cap type: case variables match
  ;; should the type of Cap change?
  [(type-substp (Cap P T) P loc) (Cap loc (type-substp T P loc))]
  [(type-substp (Cap loc_1 T) P loc) (Cap loc_1 (type-substp T P loc))]
  ;; Possible variable capture cases
  ;; case ∀1: subst on bounded variable. No effect.
  [(type-substp (∀ P T) P loc) (∀ P T)]
  ;; case ∀2: P_0 not in FLV(loc), no capture risk. Consider two sub-cases:
  ;; 1) loc = location constant. Proceed with substitution
  [(type-substp (∀ P_0 T) P_1 L) 
   (∀ P_0 (type-substp T P_1 L))]
  ;; 2) loc = P_new / P-new != P_0. Proceed with substitution.
  [(type-substp (∀ P_0 T) P_1 P_new) 
   (∀ P_0 (type-substp T P_1 P_new))
   (side-condition (not (equal? (term P_0) (term P_new))))] 
  ;; case ∀3: P_0 in FLV(loc), have to rename. This is the same as trying to 
  ;; substitute P_1 for P_0.
  [(type-substp (∀ P_0 T) P_1 P_0)
   (∀ P_2 (type-substp T_ren P_1 P_0))   
   (where P_2 ,(variable-not-in (term (P_0 T)) (term P_0)))
   (where T_ren (type-substp T P_0 P_2))]
  ;; case ∃1: subst on bounded variable. No effect.
  [(type-substp (∃ P T) P loc) (∃ P T)]
  ;; case ∃2: P_0 not in FLV(loc), no capture risk. Consider two sub-cases:
  ;; 1) loc = location constant. Proceed with substitution
  [(type-substp (∃ P_0 T) P_1 L) 
    (∃ P_0 (type-substp T P_1 L))]
  ;; 2) loc = P_new / P-new != P_0. Proceed with substitution.
  [(type-substp (∃ P_0 T) P_1 P_new) 
   (∃ P_0 (type-substp T P_1 P_new))
   (side-condition (not (equal? (term P_0) (term P_new))))] 
  ;; case ∃3: P_0 in FLV(loc), have to rename.
  [(type-substp (∃ P_0 T) P_1 P_0)
   (∃ P_2 (type-substp T_ren P_1 P_0))
   (where P_2 ,(variable-not-in (term (P_0 T)) (term P_0)))
   (where T_ren (type-substp T P_0 P_2))])



(define-judgment-form L3
  #:mode (type-alpha-eq? I I)
  #:contract (type-alpha-eq? T T)
  
  [--------------------------------------------------------- α-Unit
   (type-alpha-eq? I I)]

  
   [--------------------------------------------------------- α-Int
   (type-alpha-eq? Int Int)]
  
   [--------------------------------------------------------- α-Type-Var
   (type-alpha-eq? tX tX)]
  
  [(type-alpha-eq? T_11 T_21)
   (type-alpha-eq? T_12 T_22)
   --------------------------------------------------------- α-Mult
   (type-alpha-eq? (T_11 ⊗ T_12) (T_21 ⊗ T_22))]
  
  [(type-alpha-eq? T_11 T_21)
   (type-alpha-eq? T_12 T_22)
   --------------------------------------------------------- α-Sum
   (type-alpha-eq? (T_11 + T_12) (T_21 + T_22))]

  [(type-alpha-eq? T_11 T_21)
   (type-alpha-eq? T_12 T_22)
   --------------------------------------------------------- α-Fun
   (type-alpha-eq? (T_11 -o T_12) (T_21 -o T_22))]

  [(type-alpha-eq? T_1 T_2)
   --------------------------------------------------------- α-Bang
   (type-alpha-eq? (! T_1) (! T_2))]

  ;; Pointers with location constant are eq iff constants 
  ;; are the same.
  [--------------------------------------------------------- α-Ptr-Const
   (type-alpha-eq? (Ptr L) (Ptr L))]
  
  ;; If location variables are the same, then pointers are
  ;; equivalent.
  [--------------------------------------------------------- α-Ptr-Var
   (type-alpha-eq? (Ptr P) (Ptr P))]
   

  ;; Capabilities with constant locations are eq iff their 
  ;; types are eq
  [(type-alpha-eq? T_1 T_2)
   --------------------------------------------------------- α-Cap-Const
   (type-alpha-eq? (Cap L T_1) (Cap L T_2))]

  ;; If location variables are the same, capabilities are  
  ;; eq iff types are eq
  [(type-alpha-eq? T_1 T_2)
   --------------------------------------------------------- α-Cap-Eq-Var
   (type-alpha-eq? (Cap P T_1) (Cap P T_2))]
  
  ;; ∀ expressions are equivalent iff their substitution 
  ;; with a fresh variable is equivalent. 
  [(where P_3 
          ,(variable-not-in 
            (term ((type-FreeLocs T_1) (type-FreeLocs T_2))) 
            (term P_1)))
   (type-alpha-eq? 
    (type-substp T_1 P_1 P_3) (type-substp T_2 P_2 P_3))
   --------------------------------------------------------- α-Forall
   (type-alpha-eq? 
    (∀ P_1 T_1) (∀ P_2 T_2))]

  ;; ∃ expressions are equivalent iff their substitution 
  ;; with a fresh variable is equivalent.
  [(where P_3 
          ,(variable-not-in 
            (term ((type-FreeLocs T_1) (type-FreeLocs T_2))) 
            (term P_1)))
   (type-alpha-eq? 
    (type-substp T_1 P_1 P_3) (type-substp T_2 P_2 P_3))
   --------------------------------------------------------- α-Exists
   (type-alpha-eq?
    (∃ P_1 T_1) (∃ P_2 T_2))])


(define (alpha-eq-T? t1 t2)
  (judgment-holds (type-alpha-eq? ,t1 ,t2)))

;; -----------------------------------------------------------------------------
;; Type substitution (for recursive types)
;; -----------------------------------------------------------------------------

(define-metafunction L3
  type-FV-acc : (tX ...) T -> (tX ...)
  [(type-FV-acc (tX_env ...) I) ()]
  [(type-FV-acc (tX_env ...) Int) ()]
  [(type-FV-acc (tX_env1 ... tX tX_env2 ...) tX) ()]
  [(type-FV-acc (tX_env ...) tX) (tX)] 
  [(type-FV-acc (tX_env ...) (T_1 ⊗ T_2)) 
   (tX_1 ... tX_2 ...)
   (where (tX_1 ...) (type-FV-acc (tX_env ...) T_1))
   (where (tX_2 ...) (type-FV-acc (tX_env ...) T_2))]
  [(type-FV-acc (tX_env ...) (T_1 + T_2)) 
   (tX_1 ... tX_2 ...)
   (where (tX_1 ...) (type-FV-acc (tX_env ...) T_1))
   (where (tX_2 ...) (type-FV-acc (tX_env ...) T_2))]
  [(type-FV-acc (tX_env ...) (T_1 -o T_2))
   (tX_1 ... tX_2 ...)
   (where (tX_1 ...) (type-FV-acc (tX_env ...) T_1))
   (where (tX_2 ...) (type-FV-acc (tX_env ...) T_2))]
  [(type-FV-acc (tX_env ...) (! T)) 
   (type-FV-acc (tX_env ...) T)]
  [(type-FV-acc (tX_env ...) (Ptr loc)) ()]
  [(type-FV-acc (tX_env ...) (Cap P T))
   (type-FV-acc (tX_env ...) T)]
  [(type-FV-acc (tX_env ...) (∀ P T)) 
   (type-FV-acc (tX_env ...) T)]
  [(type-FV-acc (tX_env ...) (∃ P T)) 
   (type-FV-acc (tX_env ...) T)]
  [(type-FV-acc (tX_env ...) (μ tX T))
   (type-FV-acc (tX tX_env ...) T)])


(define-metafunction L3
  type-FV : T -> (tX ...)
  [(type-FV T) 
   ,(remove-duplicates (term (type-FV-acc () T)))])



;; Type substitution for types
(define-metafunction L3
  type-subst : T_in tX T_new -> T_out
  [(type-subst I tX T_new) I]
  [(type-subst Int tX T_new) Int]
  [(type-subst tX tX T_new) T_new]
  [(type-subst tX_in tX T_new) tX_in]
  [(type-subst (T_1 ⊗ T_2) tX T_new) 
   ((type-subst T_1 tX T_new) ⊗ (type-subst T_2 tX T_new))]
  [(type-subst (T_1 + T_2) tX T_new) 
   ((type-subst T_1 tX T_new) + (type-subst T_2 tX T_new))]
  [(type-subst (T_1 -o T_2) tX T_new) 
   ((type-subst T_1 tX T_new) -o (type-subst T_2 tX T_new))]
  [(type-subst (! T) tX T_new) (! (type-subst T tX T_new))]
  [(type-subst (Ptr loc) tX T_new) (Ptr loc)]
  [(type-subst (Cap loc T) tX T_new) 
   (Cap loc (type-subst T tX T_new))]
  [(type-subst (∀ P T) tX T_new) 
   (∀ P (type-subst T tX T_new))]
  [(type-subst (∃ P T) tX T_new) 
   (∃ P (type-subst T tX T_new))]
  ;; Case μ1 : Substitution for the bounded variable.
  [(type-subst (μ tX T) tX T_new)
   (μ tX T)]
  ;; Case μ2 : Bounded variable is not in FV(T_new)
  [(type-subst (μ tX_b T) tX T_new) 
   (μ tX_b (type-subst T tX T_new))
   (side-condition (not (member? (term tX_b) (term (type-FV T_new)))))] 
  ;; Case μ3: Bounded variable in FLV(T), have to rename.
  [(type-subst (μ tX_b T) tX T_new)
   (μ tX_fresh (type-subst T_ren tX T_new))
   (where tX_fresh ,(variable-not-in (term (tX_b T T_new)) (term tX_b)))
   (where T_ren (type-substp T tX_b tX_fresh))])


;; -----------------------------------------------------------------------------
;; TESTS

(module+ test
  
  (define type_1
    (term
     ((Ptr p_1) ⊗ (Ptr p_2))))
  
  
  (define type_2
    (term
     (∀ p_bound ((Cap p_bound I) -o 
                (((! (Ptr p_bound)) ⊗ (! (Ptr p_bound))) -o 
                (I -o 
                (((Cap p_bound I) ⊗ (! (Ptr p_bound))) ⊗ I)))))))
  
  
  (define type_3
    (term
     (∀ p_bound ((Cap p_bound I) -o 
                (((! (Ptr p_not_bound)) ⊗ (! (Ptr p_not_bound))) -o 
                (I -o 
                (((Cap p_bound I) ⊗ (! (Ptr p_bound))) ⊗ I)))))))
  
  
 
  (redex-match? L3 T type_1) 
  ;; Simple substitution without quantifiers
  (test-equal (term (type-substp ,type_1 p_1 p_new)) 
              (term ((Ptr p_new) ⊗ (Ptr p_2))))
  
  ;; Location type substitution case ∀1 
  (redex-match? L3 T type_2) 
  (test-equal (term (type-substp ,type_2 p_bound p_new)) 
              (term (∀ p_bound 
                       ((Cap p_bound I) -o 
                       (((! (Ptr p_bound)) ⊗ (! (Ptr p_bound))) -o 
                       (I -o 
                       (((Cap p_bound I) ⊗ (! (Ptr p_bound))) ⊗ I)))))))
  
  ;; Location type substitution case ∀2
  (redex-match? L3 T type_3) 
  (test-equal (term (type-substp ,type_3 p_not_bound p_new)) 
              (term (∀ p_bound 
                       ((Cap p_bound I) -o 
                       (((! (Ptr p_new)) ⊗ (! (Ptr p_new))) -o 
                       (I -o 
                       (((Cap p_bound I) ⊗ (! (Ptr p_bound))) ⊗ I)))))))
  
  
  ;; Location type substitution case ∀3. Check equality modulo α-conversion.
  (test-equal (term (type-substp ,type_3 p_not_bound p_bound)) 
              (term (∀ p_new_bound 
                       ((Cap p_new_bound I) -o 
                       (((! (Ptr p_bound)) ⊗ (! (Ptr p_bound))) -o 
                       (I -o 
                       (((Cap p_new_bound I) ⊗ (! (Ptr p_new_bound))) ⊗ I))))))
              #:equiv alpha-eq-T?)
  
  (define list-type
    (term
     (I + (Int ⊗ (∃ p ((Cap p α) ⊗ (! (Ptr p))))))))
  
  (define rec-list-type
    (term
      (μ α ,list-type)))
  
  (redex-match? L3 T list-type)
  (redex-match? L3 T rec-list-type)
  
  (test-equal (term (type-subst ,list-type α ,list-type))
              (term (I + (Int ⊗ (∃ p ((Cap p 
                    (I + (Int ⊗ (∃ p1 ((Cap p1 α) ⊗ (! (Ptr p1)))))))
                                      ⊗ (! (Ptr p)))))))
              #:equiv alpha-eq-T?)
  
)
   





