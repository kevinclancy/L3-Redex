#lang racket
(require redex)

(define-language L3
  ;expressions
  (e *
     (let * = e in e)
     (e / e) ;pair
     (let (x / x) = e in e) ;pair elimination
     x
     (λ (x T) e) ;abstraction
     (e e) ;application
     (! v)
     (let (! x) = e in e)
     (dupl e)
     (drop e)
     (ptr lconst)
     cap
     (new e)
     (free e)
     (swap e e e)
     (Λ p e) ;location abstraction. to type a Λ, type \Lambda followed by alt-\ in Dr. Racket
     (e loc) ;location application
     (loc // e) ;location package
     (let (p // x) = e in e)) ;open location package
  (x a b c variable-not-otherwise-mentioned) ;term variable
  (l m n) ;location constant
  (p q r) ;location variable
  (loc l p) ;location constant or variable
  ;values
  (v *
     (v / v)
     x
     (λ (x T) e)
     (! v)
     (ptr l)
     cap
     (Λ p e)
     (loc // v))
  ;types
  (T I ;unit
     (T ⊗ T) ;tensor product. \otimes + alt-\ gives ⊗
     (T -o T) ;linear function
     (! T) ; unrestricted "of course" type
     (Ptr loc) ;type of pointer to location w
     (Cap loc T) ;capability for location w, where the value stored at w has type T
     (∀ p T) ; location abstraction type
     (∃ p T)); location package type
  (store ((l v) ...))
  ;evaluation contexts
  (E hole
     (let * = E in e)
     (E / e)
     (v / E)
     (let (x / x) = E in e)
     (E e)
     (v E)
     (let (! x) = E in e)
     (dupl E)
     (drop E)
     (new E)
     (free E)
     (swap E e e)
     (swap v E e)
     (swap v v E)
     (E l)
     (lconst // E)
     (let (p // x) = E in e)))



(define-language lc-lang
  (e (e e ...)
     x
     v)
  (c (v ... c e ...)
     hole)
  (v (λ (x ...) e))
  (x variable-not-otherwise-mentioned))

(define-metafunction lc-lang
  - : (x ...) (x ...) -> (x ...)
  [(- (x ...) ()) (x ...)]
  [(- (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (- (x_1 ... x_3 ...) (x_2 x_4 ...))
   (where (x ...) (x_1 ...))]
  [(- (x_1 ...) (x_2 x_3 ...))
   (- (x_1 ...) (x_3 ...))])


;;auxiliary function for FreeVars
(define-metafunction L3
  FV : (x ...) e -> (x ...)
  [(FV (x ...) *) ()]
  [(FV (x ...) (let * = e_1 in e_2))
   (x_fv1 ... x_fv2 ...) 
   (where (x_fv1 ...) (FV (x ...) e_1))
   (where (x_fv2 ...) (FV (x_fv1 ... x ...) e_2))]  
  [(FV (x ...) (e_1 / e_2))
   (x_fv1 ... x_fv2 ...)
   (where (x_fv1 ...) (FV (x ...) e_1))
   (where (x_fv2 ...) (FV (x_fv1 ... x ...) e_2))]
  [(FV (x ...) (let (x_1 / x_2) = e_1 in e_2))
   (x_fv1 ... x_fv2 ...) 
   (where (x_fv1 ...) (FV (x ...) e_1))
   (where (x_fv2 ...) (FV (x_1 x_2 x_fv1 ... x ...) e_2))]
  ; variable that is bound in environment
  [(FV (x_env1 ... x_term x_env2 ...) x_term) ()]
  ; variable that is not bound in environment
  [(FV (x_env ...) x_term) (x_term)]
  [(FV (x_env ...) (λ (x T) e)) (FV (x x_env ...) e)]
  [(FV (x ...) (e_1 e_2)) 
   (x_fv1 ... x_fv2 ...)
   (where (x_fv1 ...) (FV (x ...) e_1))
   (where (x_fv2 ...) (FV (x_fv1 ... x ...) e_2))]
  [(FV (x_env1 ... x x_env2 ...) (! x)) ()]
  [(FV (x_env ...) (! x)) (x)]
  [(FV (x_env ...) (let (! x) = e_1 in e_2))
   (x_fv1 ... x_fv2 ...)
   (where (x_fv1 ...) (FV (x_env ...) e_1))
   (where (x_fv2 ...) (FV (x x_fv1 ... x_env ...) e_2))]
  [(FV (x ...) (dupl e)) (FV (x ...) e)]
  [(FV (x ...) (drop e)) (FV (x ...) e)]
  [(FV (x ...) (ptr l)) ()]
  [(FV (x ...) cap) ()]
  [(FV (x ...) (new e)) (FV (x ...) e)] 
  [(FV (x ...) (free e)) (FV (x ...) e)]
  [(FV (x ...) (swap e_1 e_2 e_3))
   (x_fv1 ... x_fv2 ... x_fv3 ...)
   (where (x_fv1 ...) (FV (x ...) e_1))
   (where (x_fv2 ...) (FV (x_fv1 ... x ...) e_2))
   (where (x_fv3 ...) (FV (x_fv1 ... x_fv2 ... x ...) e_3))]
  [(FV (x ...) (Λ p e)) (FV (x ...) e)]
  [(FV (x ...) (e loc)) (FV (x ...) e)]
  [(FV (x ...) (loc // e)) (FV (x ...) e)]
  [(FV (x_env ...) (let (loc // x) = e_1 in e_2))
   (x_fv1 ... x_fv2 ...)
   (where (x_fv1 ...) (FV (x_env ...) e_1))
   (where (x_fv2 ...) (FV (x x_fv1 ... x_env ...) e_2))])

; returns list (from left to right) of all free variables of input expression
(define-metafunction L3
  FreeVars : e -> (x ...)
  [(FreeVars e) (FV () e)])
  
(module+ test
  (require rackunit)
  (check-equal? (term (FreeVars (λ (a I) *))) '())
  (check-equal? (term (FreeVars ((λ (a I) b) a))) '(b a))
  (check-equal? (term (FreeVars (let (a / b) = (a c) in (b c)))) '(a c)))

(define-metafunction L3
  FL : (p ...) e -> (p ...)
  [(FL (p ...) *) ()]
  [(FL (p ...) (let * = e_1 in e_2))
   (p_fp1 ... p_fp2 ...) 
   (where (p_fp1 ...) (FL (p ...) e_1))
   (where (p_fp2 ...) (FL (p_fp1 ... p ...) e_2))]  
  [(FL (p ...) (e_1 / e_2))
   (p_fp1 ... p_fp2 ...)
   (where (p_fp1 ...) (FL (p ...) e_1))
   (where (p_fp2 ...) (FL (p_fp1 ... p ...) e_2))]
  [(FL (p ...) (let (x_1 / x_2) = e_1 in e_2))
   (p_fp1 ... p_fp2 ...) 
   (where (p_fp1 ...) (FL (p ...) e_1))
   (where (p_fp2 ...) (FL (p_fp1 ... p ...) e_2))]
  [(FL (p ...) x) ()]
  [(FL (p ...) (λ (x T) e)) (FL (p ...) e)]
  [(FL (p ...) (e_1 e_2)) 
   (p_fp1 ... p_fp2 ...)
   (where (p_fp1 ...) (FL (p ...) e_1))
   (where (p_fp2 ...) (FL (p_fp1 ... p ...) e_2))]
  [(FL (p ...) (! x)) ()]
  [(FL (p ...) (let (! x) = e_1 in e_2))
   (p_fp1 ... p_fp2 ...)
   (where (p_fp1 ...) (FL (p ...) e_1))
   (where (p_fp2 ...) (FL (p_fp1 ... p ...) e_2))]
  [(FL (p ...) (dupl e)) (FL (p ...) e)]
  [(FL (p ...) (drop e)) (FL (p ...) e)]
  [(FL (p_1 ... l p_2 ...) (ptr l)) ()]
  [(FL (p ...) (ptr l)) (l)]
  [(FL (p ...) cap) ()]
  [(FL (p ...) (new e)) (FL (p ...) e)] 
  [(FL (p ...) (free e)) (FL (p ...) e)]
  [(FL (p ...) (swap e_1 e_2 e_3))
   (p_fp1 ... p_fp2 ... p_fp3 ...)
   (where (p_fp1 ...) (FL (p ...) e_1))
   (where (p_fp2 ...) (FL (p_fp1 ... p ...) e_2))
   (where (p_fp3 ...) (FL (p_fp1 ... p_fp2 ... p ...) e_3))]
  [(FL (p_env ...) (Λ p e)) (FL (p p_env ...) e)]
  [(FL (p_env ...) (e l)) (FV (p_env ...) e)] 
  [(FL (p_env ...) (e p)) 
   (p_e ... p)
   (where (p_e ...) (FV (p_env ...) e))]
  [(FL (p ...) (l // e)) (FV (p ...) e)]
  [(FL (p_env1 ... p p_env2 ...) (p // e)) 
   (p_e ...)
   (where (p_e ...) (FL (p_env1 ... p p_env2 ...) e))]
  [(FL (p_env ...) (p // e))
   (p p_e ...)
   (where (p_e ...) (FL (p_env ...) e))]
  [(FL (p_env ...) (let (p // x) = e_1 in e_2))
   (p_fp1 ... p_fp2 ...)
   (where (p_fp1 ...) (FV (p_env ...) e_1))
   (where (p_fp2 ...) (FV (p p_fp1 ... p_env ...) e_2))])


(define-metafunction L3
  FreeLocVars : e -> (loc ...)
  [(FreeLocVars e) (FL () e)])

;location substitution for types
(define-metafunction L3
  type-substp : T_in p loc -> T_out
  [(type-substp I p loc) I]
  [(type-substp (T_1 ⊗ T_2) p loc) ((type-substp T_1 p loc) ⊗ (type-substp T_2 p loc))]
  [(type-substp (T_1 -o T_2) p loc) ((type-substp T_1 p loc) -o (type-substp T_2 p loc))]
  [(type-substp (! T) p loc) (! (type-substp T p loc))]
  [(type-substp (Ptr p) p loc) (Ptr loc)]
  [(type-substp (Ptr p_1) p loc) (Ptr p_1)]
  [(type-substp (Cap p T) p loc) (Cap loc (type-substp T p loc))]
  [(type-substp (Cap p_1 T) p loc) (Cap p_1 (type-substp T p loc))]
  [(type-substp (∀ p T) p loc) (∀ p T)]
  [(type-substp (∀ p_1 T) p loc) (∀ p (type-substp T p loc))]
  [(type-substp (∃ p T) p loc) (∃ p T)]
  [(type-substp (∃ p_1 T) p loc) (∃ p_1 (type-substp T p loc))])

  
; TODO: attach type ascriptions to let bindings?
(define-metafunction L3
  ;substitute loc for p in e_in
  substp : e_in p loc -> e_out
  [(substp * p loc) *]
  [(substp (let * = e_11 in e_12) p loc)
   (let * = (substp e_11 p loc) in (substp e_12 p loc))]
  [(substp (e_11 / e_12) p loc) ((substp e_11 p loc) / (substp e_12 p loc))]
  [(substp (let (x_1 / x_2) = e_11 in e_12) p loc)
   (let (x_1 / x_2) = (substp e_11 p loc) in (subspt e_12 p loc))]
  [(substp x p loc) x]
  [(substp (λ (x_1 T) e_11) x v) 
   (λ (x_1 (type-substp T p loc)) (substp e_11 p loc))]
  [(substp (e_11 e_12) p loc) ((substp e_11 p loc) (substp e_12 p loc))]
  [(substp (! x) p loc) (! x)]
  [(substp (let (! x) = e_11 in e_12) p loc) 
   (let (! x) = (substp e_11 p loc) in (substp e_12 p loc))]
  [(substp (dupl e) p loc) (dupl (substp e p loc))]
  [(substp (drop e) p loc) (drop (substp e p loc))]
  [(substp (ptr l) p loc) (ptr l)]
  [(substp cap p loc) cap]
  [(substp (new e) p loc) (new (substp e p loc))]
  [(substp (free e) p loc) (free (substp e p loc))]
  [(substp (swap e_1 e_2 e_3)) (swap (substp e_1 p loc) (subst e_2 p loc) (subst e_3 p loc))]
  [(substp (Λ p e) p loc) (Λ p e)]
  [(substp (Λ p_1 e) p loc) (Λ p_1 (substp e p loc))]
  [(substp (e p) p loc) ((substp e p loc) loc)]
  [(substp (e loc_1) p loc) ((substp e p loc) loc_1)]
  [(substp (p // e) p loc) (loc // (substp e p loc))]
  [(substp (loc_1 // e) p loc) (loc_1 // (substp e p loc))]
  [(substp (let (p // x) = e_1 in e_2) p loc)
   (let (p // x) = (substp e_1 p loc) in e_2)]
  [(substp (let (p_1 // x) = e_1 in e_2) p loc)
   (let (p_1 // x) = (substp e_1 p loc) in (substp e_2 p loc))]
  )


(define-metafunction L3
  ;substitute v for all occurences of x in e_1
  subst : e_1 x v -> e
  [(subst * x v) *]
  [(subst (let * = e_11 in e_12) x v)
   (let * = (subst e_11 x v) in (subst e_12 x v))]
  [(subst (e_11 / e_12) x v) ((subst e_11 x v) / (subst e_12 x v))]
  [(subst (let (x / x_1) = e_11 in e_12) x v) 
   (let (x_1 / x_2) = (subst e_11 x v) in e_12)]
  [(subst (let (x_1 / x) = e_11 in e_12) x v) 
   (let (x_1 / x_2) = (subst e_11 x v) in e_12)]
  [(subst (let (x_1 / x_2) = e_11 in e_12) x v)
   (let (x_1prime / x_2prime) = (subst e_11 x v) in x (subst (subst e_12 x_1 x_1prime) x_2 x_2prime))
   (where x_1prime ,(variable-not-in (term ((FreeVars e_11) (FreeVars e_12) (FreeVars v) x)) (term x_1)))
   (where x_2prime ,(variable-not-in (term ((FreeVars e_11) (FreeVars e_12) (FreeVars v) x x_1prime)) (term x_2)))]
  [(subst x x v) v]
  [(subst x_1 x v) x_1]
  [(subst (λ (x T) e_11) x v) (λ (x T) e_11)] 
  [(subst (λ (x_1 T) e_11) x v) 
   (λ (x_1prime T) (subst e_11 x (subst e_11 x_1 x_1prime) v))
   (where x_1prime ,(variable-not-in (term ((FreeVars e_11) (FreeVars e_12) (FreeVars v) x)) (term x_1)))]
  [(subst (e_11 e_12) x v) ((subst e_11 x v) (subst e_12 x v))]
  [(subst (! x) x v) (! v)]
  [(subst (! v_1) x v) (! v_1)]
  [(subst (let (! x) = e_11 in e_12) x v) (let (! x) = e_11 in e_12)]
  [(subst (let (! x_1) = e_11 in e_12) x v)
   (let (! x_1prime) = (subst e_11 x v) in (subst (subst e_12 x_1 x_1prime) x v))
   (where x_1prime ,(variable-not-in (term (v (FreeVars e_11) (FreeVars e_12))) (term x_1)))]
  [(subst (dupl e) x v) (dupl (subst e x v))]
  [(subst (drop e) x v) (drop (subst e x v))]
  [(subst (ptr l) x v) (ptr l)]
  [(subst cap x v) cap]
  [(subst (new e) x v) (new (subst e x v))]
  [(subst (free e) x v) (free (subst e x v))]
  [(subst (swap e_1 e_2 e_3)) (swap (subst e_1 x v) (subst e_2 x v) (subst e_3 x v))]
  [(subst (Λ p e) x v) 
   (Λ p_prime (subst (substp e p p_prime) x v))
   (where (p_prime) ,(variable-not-in (term ((FreeLocVars e) (FreeLocVars v)))))]
  [(subst (e loc) x v) ((subst e x v) loc)]
  [(subst (loc // e) x v) (loc // (subst e x v))]
  [(subst (let (p // x) = e_1 in e_2) x v)
   (let (p_prime // x) = (subst e_1 x v) in (subst (substp e_2 p p_prime) x v))
   (where (p_prime) ,(variable-not-in (term ((FreeLocVars e_2) (FreeLocVars v)))))]
  )

(define-judgment-form L3
  #:mode (type-alpha-eq? I I)
  #:contract (type-alpha-eq? T T)
  [-------------------
   (type-alpha-eq? I I)]
  [(type-alpha-eq? T_11 T_21)
   (type-alpha-eq? T_12 T_22)
   -------------------
   (type-alpha-eq? (T_11 ⊗ T_12) (T_21 ⊗ T_22))]
  [(type-alpha-eq? T_11 T_21)
   (type-alpha-eq? T_12 T_22)
   -------------------
   (type-alpha-eq? (T_11 -o T_12) (T_21 -o T_22))]
  [(type-alpha-eq? T_1 T_2)
   -------------------
   (type-alpha-eq? (! T_1) (! T_2))]
  [-------------------
   (type-alpha-eq? (Ptr l) (Ptr l))]
  [(type-alpha-eq? T_1 T_2)
   -------------------
   (type-alpha-eq? (Cap l T_1) (Cap l T_2))]
  [(where p_3 ,(variable-not-in (term ((FreeLocVars T_1) (FreeLocVars T_2)))))
   (type-alpha-eq? (substp T_1 p_1 p_3) (substp T_2 p_2 p_3))
   -------------------
   (type-alpha-eq? (∀ p_1 T_1) (∀ p_2 T_2))]
  [(where p_3 ,(variable-not-in (term ((FreeLocVars T_1) (FreeLocVars T_2)))))
   (type-alpha-eq? (substp T_1 p_1 p_3) (substp T_2 p_2 p_3))
   -------------------
   (type-alpha-eq? (∃ p_1 T_1) (∃ p_2 T_2))])
     
(define-judgment-form L3
  #:mode (alpha-eq? I I)
  #:contract (alpha-eq? e e)
  [-------------------
   (alpha-eq? * *)]
  [(alpha-eq? e_11 e_21)
   (alpha-eq? e_12 e_22)
   -------------------
   (alpha-eq? (let * = e_11 in e_12) (let * = e_21 in e_22))]
  [(alpha-eq? e_11 e_21)
   (alpha-eq? e_12 e_22)
   -------------------
   (alpha-eq? (e_11 / e_12) (e_21 / e_22))]
  [(where x_31 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term x_11)))
   (where x_32 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term x_12)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst (subst e_12 x_11 x_31) x_12 x_32) 
                     (subst (subst e_22 x_21 x_31) x_22 x_32))
   -------------------
   (alpha-eq? (let (x_11 / x_12) = e_11 in e_12) (let (x_21 / x_22) = e_21 in e_22))]
  [-------------------
   (alpha-eq? x x)]
  [(where x_3 ,(variable-not-in (term ((FreeVars e_1) (FreeVars e_2))) (term x_1)))
   (alpha-eq? (subst e_1 x_1 x_3) (subst e_2 x_2 x_3))
   (type-alpha-eq? T_1 T_2)
   -------------------
   (alpha-eq? (λ (x_1 T_1) e_1) (λ (x_2 T_2) e_2))]
  [(alpha-eq? e_11 e_21) 
   (alpha-eq? e_12 e_22)
   -------------------
   (alpha-eq? (e_11 e_12) (e_21 e_22))]
  [(alpha-eq? v_1 v_2)
   -------------------
   (alpha-eq? (! v_1) (! v_2))]
  [(where x_3 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term x_1)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst e_12 x_1 x_3) (subst e_22 x_2 x_3))
   -------------------
   (alpha-eq? (let (! x_1) = e_11 in e_12) (let (! x_2) = e_21 in e_22))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (dupl e_1) (dupl e_2))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (drop e_1) (drop e_2))]
  [-------------------
   (alpha-eq? (ptr l) (ptr l))]
  [-------------------
   (alpha-eq? cap cap)]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (new e_1) (new e_2))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (free e_1) (free e_2))]
  [(alpha-eq? e_11 e_21)
   (alpha-eq? e_12 e_22)
   (alpha-eq? e_13 e_23)
   -------------------
   (alpha-eq? (swap e_11 e_12 e_13) (swap e_21 e_22 e_23))]
  [(where p_3 ,(variable-not-in (term ((FreeLocVars e_1) (FreeLocVars e_2))) (term p_1)))
   (alpha-eq? (substp e_1 p_1 p_3) (substp e_2 p_2 p_3))
   -------------------
   (alpha-eq? (Λ p_1 e_1) (Λ p_2 e_2))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (e_1 loc) (e_2 loc))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (loc // e_1) (loc // e_2))]
  [(where x_3 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term x_1)))
   (where p_3 ,(variable-not-in (term ((FreeLocVars e_12) (FreeLocVars e_22))) (term p_1)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst (substp e_12 p_1 p_3) x_1 x_3) (subst (substp e_22 p_2 p_3) x_2 x_3))
   -------------------
   (alpha-eq? (let (p_1 // x_1) = e_11 in e_12) (let (p_2 // x_2) = e_21 in e_22))])

(module+ test
  (test-equal (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in y))) #t)
  (test-equal (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in x))) #f)
  (test-equal (judgment-holds (alpha-eq? (let (! x) = (λ (y I) y) in x) (let (! y) = (λ (z I) z) in y))) #t)
  
  )

(define



(define ->L3 
  (reduction-relation 
   L3 
   #:domain (store e)
   (-->
    (store (let * = * in e)) 
    (store e))))

   ;(-->
   ; (store (let (x_1 / x_2) = (v_1 / v_2) in e))
   ; (store (
    
                      
     
     
     


        
        