#lang racket
(require redex)
(require racket/set)

(define-language L3
  ;expressions
  (e *
     (let * = e in e)
     (e / e) ;pair
     (let (X / X) = e in e) ;pair elimination
     X
     (λ (X T) e) ;abstraction
     (e e) ;application
     (! v)
     (let (! X) = e in e)
     (dupl e)
     (drop e)
     (ptr L)
     cap
     (new e)
     (free e)
     (swap e e e)
     (Λ P e) ;location abstraction. to type a Λ, type \Lambda followed by alt-\ in Dr. Racket
     (e loc) ;location application
     (loc // e) ;location package
     (let (P // X) = e in e)) ;open location package
  (X x y z (variable-prefix x) (variable-prefix y) (variable-prefix z)) ;term variable
  (loc L P) ;location constant or variable
  (L l m n (variable-prefix l) (variable-prefix m) (variable-prefix n)) ;location constant
  (P p q r (variable-prefix p) (variable-prefix q) (variable-prefix r)) ;location variable
  ;values
  (v *
     (v / v)
     X
     (λ (X T) e)
     (! v)
     (ptr L)
     cap
     (Λ P e)
     (loc // v))
  ;types
  (T I ;unit
     (T ⊗ T) ;tensor product. \otimes + alt-\ gives ⊗
     (T -o T) ;linear function
     (! T) ; unrestricted "of course" type
     (Ptr loc) ;type of pointer to location w
     (Cap loc T) ;capability for location w, where the value stored at w has type T
     (∀ P T) ; location abstraction type
     (∃ P T)); location package type
  (store ((L v) ...))
  (U ♭ ♯) ; \flat = ♭ means unused, \sharp = ♯ means used
  (type-env ((U X T) ...))
  (loc-env (P ...))
  ;evaluation contexts
  (E hole
     (let * = E in e)
     (E / e)
     (v / E)
     (let (X / X) = E in e)
     (E e)
     (v E)
     (let (! X) = E in e)
     (dupl E)
     (drop E)
     (new E)
     (free E)
     (swap E e e)
     (swap v E e)
     (swap v v E)
     (E L)
     (L // E)
     (let (P // X) = E in e)))

;;auxiliary function for FreeVars
(define-metafunction L3
  FV : (X ...) e -> (X ...)
  [(FV (X ...) *) ()]
  [(FV (X ...) (let * = e_1 in e_2))
   (X_fv1 ... X_fv2 ...) 
   (where (X_fv1 ...) (FV (X ...) e_1))
   (where (X_fv2 ...) (FV (X_fv1 ... X ...) e_2))]  
  [(FV (X ...) (e_1 / e_2))
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV (X ...) e_1))
   (where (X_fv2 ...) (FV (X_fv1 ... X ...) e_2))]
  [(FV (X ...) (let (X_1 / X_2) = e_1 in e_2))
   (X_fv1 ... X_fv2 ...) 
   (where (X_fv1 ...) (FV (X ...) e_1))
   (where (X_fv2 ...) (FV (X_1 X_2 X_fv1 ... X ...) e_2))]
  ; variable that is bound in environment
  [(FV (X_env1 ... X_term X_env2 ...) X_term) ()]
  ; variable that is not bound in environment
  [(FV (X_env ...) X_term) (X_term)]
  [(FV (X_env ...) (λ (X T) e)) (FV (X X_env ...) e)]
  [(FV (X ...) (e_1 e_2)) 
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV (X ...) e_1))
   (where (X_fv2 ...) (FV (X_fv1 ... X ...) e_2))]
  [(FV (X_env1 ... X X_env2 ...) (! X)) ()]
  [(FV (X_env ...) (! X)) (X)]
  [(FV (X_env ...) (! v)) ()]
  [(FV (X_env ...) (let (! X) = e_1 in e_2))
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV (X_env ...) e_1))
   (where (X_fv2 ...) (FV (X X_fv1 ... X_env ...) e_2))]
  [(FV (X ...) (dupl e)) (FV (X ...) e)]
  [(FV (X ...) (drop e)) (FV (X ...) e)]
  [(FV (X ...) (ptr L)) ()]
  [(FV (X ...) cap) ()]
  [(FV (X ...) (new e)) (FV (X ...) e)] 
  [(FV (X ...) (free e)) (FV (X ...) e)]
  [(FV (X ...) (swap e_1 e_2 e_3))
   (X_fv1 ... X_fv2 ... X_fv3 ...)
   (where (X_fv1 ...) (FV (X ...) e_1))
   (where (X_fv2 ...) (FV (X_fv1 ... X ...) e_2))
   (where (X_fv3 ...) (FV (X_fv1 ... X_fv2 ... X ...) e_3))]
  [(FV (X ...) (Λ p e)) (FV (X ...) e)]
  [(FV (X ...) (e loc)) (FV (X ...) e)]
  [(FV (X ...) (loc // e)) (FV (X ...) e)]
  [(FV (X_env ...) (let (loc // X) = e_1 in e_2))
   (X_fv1 ... X_fv2 ...)
   (where (X_fv1 ...) (FV (X_env ...) e_1))
   (where (X_fv2 ...) (FV (X X_fv1 ... X_env ...) e_2))])

; returns list (from left to right) of all free variables of input expression
(define-metafunction L3
  FreeVars : e -> (X ...)
  [(FreeVars e) (FV () e)])
  
;(module+ test
;  (require rackunit)
;  (check-equal? (term (FreeVars (λ (x I) *))) '())
;  (check-equal? (term (FreeVars ((λ (x I) z) y))) '(z y))
;  (check-equal? (term (FreeVars (let (x / y) = (x z) in (x y)))) '(x z)))

;     I
;     (T ⊗ T) ;tensor product. \otimes + alt-\ gives ⊗
;     (T -o T) ;linear function
;     (! T) ; unrestricted "of course" type
;     (Ptr loc) ;type of pointer to location w
;     (Cap loc T) ;capability for location w, where the value stored at w has type T
;     (∀ P T) ; location abstraction type
;     (∃ P T)); location package type

(define-metafunction L3
  type-FL : (loc ...) T -> (loc ...)
  [(type-FL (loc ...) I) ()]
  [(type-FL (loc ...) (T_1 ⊗ T_2)) 
   (loc_FL1 ... loc_FL2 ...)
   (where (loc_FL1 ...) (type-FL (loc ...) T_1))
   (where (loc_FL2 ...) (type-FL (loc ... loc_FL1 ...) T_2))]
  [(type-FL (loc ...) (T_1 -o T_2))
   (loc_FL1 ... loc_FL2 ...)
   (where (loc_FL1 ...) (type-FL (loc ...) T_1))
   (where (loc_FL2 ...) (type-FL (loc ... loc_FL1 ...) T_2))]
  [(type-FL (loc ...) (! T)) (type-FL (loc ...) T)]
  [(type-FL (loc_env1 ... loc loc_env2 ...) (Ptr loc)) ()]
  [(type-FL (loc_env ...) (Ptr loc)) (loc)]
  [(type-FL (loc_env1 ... loc loc_env2 ...) (Cap loc T)) (type-FL (loc_env1 ... loc loc_env2 ...) T)]
  [(type-FL (loc_env ...) (Cap loc T)) 
   (loc loc_T ...)
   (where (loc_T ...) (type-FL (loc loc_env ...) T))]
  [(type-FL (loc_env ...) (∀ P T)) (type-FL (loc loc_env ...) T)]
  [(type-FL (loc_env ...) (∃ P T)) (type-FL (loc loc_env ...) T)])
  
(define-metafunction L3
  type-FreeLocs : T -> (loc ...)
  [(type-FreeLocs T) (type-FL () T)])

(define-metafunction L3
  FL : (loc ...) e -> (loc ...)
  [(FL (loc ...) *) ()]
  [(FL (loc ...) (let * = e_1 in e_2))
   (loc_floc1 ... loc_floc2 ...) 
   (where (loc_floc1 ...) (FL (loc ...) e_1))
   (where (loc_floc2 ...) (FL (loc_floc1 ... loc ...) e_2))]  
  [(FL (loc ...) (e_1 / e_2))
   (loc_floc1 ... loc_floc2 ...)
   (where (loc_floc1 ...) (FL (loc ...) e_1))
   (where (loc_floc2 ...) (FL (loc_floc1 ... loc ...) e_2))]
  [(FL (loc ...) (let (X_1 / X_2) = e_1 in e_2))
   (loc_floc1 ... loc_floc2 ...) 
   (where (loc_floc1 ...) (FL (loc ...) e_1))
   (where (loc_floc2 ...) (FL (loc_floc1 ... loc ...) e_2))]
  [(FL (loc ...) X) ()]
  [(FL (loc ...) (λ (X T) e))
   (loc_T ... loc_e ...)
   (where (loc_T ...) (type-FL (loc ...) T))
   (where (loc_e ...) (FL (loc ... loc_T ...) e))]
  [(FL (loc ...) (e_1 e_2)) 
   (loc_floc1 ... loc_floc2 ...)
   (where (loc_floc1 ...) (FL (loc ...) e_1))
   (where (loc_floc2 ...) (FL (loc_floc1 ... loc ...) e_2))]
  [(FL (loc ...) (! X)) ()]
  [(FL (loc ...) (! e)) (FL (loc ...) e)]
  [(FL (loc ...) (let (! X) = e_1 in e_2))
   (loc_floc1 ... loc_floc2 ...)
   (where (loc_floc1 ...) (FL (loc ...) e_1))
   (where (loc_floc2 ...) (FL (loc_floc1 ... loc ...) e_2))]
  [(FL (loc ...) (dupl e)) (FL (loc ...) e)]
  [(FL (loc ...) (drop e)) (FL (loc ...) e)]
  [(FL (loc_0 ... L loc_1 ...) (ptr L)) ()]
  [(FL (loc ...) (ptr L)) (L)]
  [(FL (loc ...) cap) ()]
  [(FL (loc ...) (new e)) (FL (loc ...) e)] 
  [(FL (loc ...) (free e)) (FL (loc ...) e)]
  [(FL (loc ...) (swap e_1 e_2 e_3))
   (loc_floc1 ... loc_floc2 ... loc_floc3 ...)
   (where (loc_floc1 ...) (FL (loc ...) e_1))
   (where (loc_floc2 ...) (FL (loc_floc1 ... loc ...) e_2))
   (where (loc_floc3 ...) (FL (loc_floc1 ... loc_floc2 ... loc ...) e_3))]
  [(FL (loc_env ...) (Λ P e)) (FL (P loc_env ...) e)]
  [(FL (loc_env0 ... loc loc_env1 ...) (e loc)) (FV (loc_env0 ... loc loc_env1 ...) e)]
  [(FL (loc_env ...) (e loc)) (loc_e ... loc)
   (where (loc_e ...) (FL (loc_env ...) e))] 
  [(FL (loc_env0 ... loc loc_env1 ...) (loc // e)) (FV (loc_env0 ... loc loc_env1 ...) e)]
  [(FL (loc_env ...) (loc // e)) 
   (loc loc_e ...)
   (where (loc_e ...) (FL (loc_env ...) e))]
  [(FL (loc_env ...) (let (P // X) = e_1 in e_2))
   (loc_floc1 ... loc_floc2 ...)
   (where (loc_floc1 ...) (FL (loc_env ...) e_1))
   (where (loc_floc2 ...) (FL (P loc_floc1 ... loc_env ...) e_2))])

(define-metafunction L3
  FreeLocs : e -> (loc ...)
  [(FreeLocs e) (FL () e)])

;location substitution for types
(define-metafunction L3
  type-substp : T_in P loc -> T_out
  [(type-substp I P loc) I]
  [(type-substp (T_1 ⊗ T_2) P loc) ((type-substp T_1 P loc) ⊗ (type-substp T_2 P loc))]
  [(type-substp (T_1 -o T_2) P loc) ((type-substp T_1 P loc) -o (type-substp T_2 P loc))]
  [(type-substp (! T) P loc) (! (type-substp T P loc))]
  [(type-substp (Ptr P) P loc) (Ptr loc)]
  [(type-substp (Ptr P_1) P loc) (Ptr P_1)]
  [(type-substp (Cap P T) P loc) (Cap loc (type-substp T P loc))]
  [(type-substp (Cap P_1 T) P loc) (Cap P_1 (type-substp T P loc))]
  [(type-substp (∀ P T) P loc) (∀ P T)]
  [(type-substp (∀ P_1 T) P loc) (∀ P (type-substp T p loc))]
  [(type-substp (∃ P T) P loc) (∃ P T)]
  [(type-substp (∃ P_1 T) P loc) (∃ P_1 (type-substp T p loc))])

  
; TODO: attach type ascriptions to let bindings?
(define-metafunction L3
  ;substitute loc for p in e_in
  substp : e_in P loc -> e_out
  [(substp * P loc) *]
  [(substp (let * = e_11 in e_12) P loc)
   (let * = (substp e_11 P loc) in (substp e_12 P loc))]
  [(substp (e_11 / e_12) P loc) ((substp e_11 P loc) / (substp e_12 P loc))]
  [(substp (let (X_1 / X_2) = e_11 in e_12) P loc)
   (let (X_1 / X_2) = (substp e_11 P loc) in (substp e_12 P loc))]
  [(substp X P loc) X]
  [(substp (λ (X T) e_11) P loc) 
   (λ (X (type-substp T P loc)) (substp e_11 P loc))]
  [(substp (e_11 e_12) P loc) ((substp e_11 P loc) (substp e_12 P loc))]
  [(substp (! X) P loc) (! X)]
  [(substp (let (! X) = e_11 in e_12) P loc) 
   (let (! X) = (substp e_11 P loc) in (substp e_12 P loc))]
  [(substp (dupl e) P loc) (dupl (substp e P loc))]
  [(substp (drop e) P loc) (drop (substp e P loc))]
  [(substp (ptr L) P loc) (ptr L)]
  [(substp cap P loc) cap]
  [(substp (new e) P loc) (new (substp e P loc))]
  [(substp (free e) P loc) (free (substp e P loc))]
  [(substp (swap e_1 e_2 e_3) P loc) (swap (substp e_1 P loc) (substp e_2 P loc) (substp e_3 P loc))]
  [(substp (Λ P e) P loc) (Λ P e)]
  [(substp (Λ P_1 e) p loc) (Λ P_1 (substp e p loc))]
  [(substp (e P) P loc) ((substp e P loc) loc)]
  [(substp (e loc_1) P loc) ((substp e P loc) loc_1)]
  [(substp (P // e) P loc) (loc // (substp e P loc))]
  [(substp (loc_1 // e) P loc) (loc_1 // (substp e P loc))]
  [(substp (let (P // X) = e_1 in e_2) P loc)
   (let (P // X) = (substp e_1 P loc) in e_2)]
  [(substp (let (P_1 // X) = e_1 in e_2) P loc)
   (let (P_1 // X) = (substp e_1 P loc) in (substp e_2 P loc))]
  )


(define-metafunction L3
  ;substitute v for all occurences of X in e_1
  subst : e_1 X v -> e
  [(subst * X v) *]
  [(subst (let * = e_11 in e_12) X v)
   (let * = (subst e_11 X v) in (subst e_12 X v))]
  [(subst (e_11 / e_12) X v) ((subst e_11 X v) / (subst e_12 X v))]
  [(subst (let (X / X_1) = e_11 in e_12) X v) 
   (let (X_1 / X_2) = (subst e_11 X v) in e_12)]
  [(subst (let (X_1 / X) = e_11 in e_12) X v) 
   (let (X_1 / X_2) = (subst e_11 X v) in e_12)]
  [(subst (let (X_1 / X_2) = e_11 in e_12) X v)
   (let (X_1prime / X_2prime) = (subst e_11 X v) in (subst (subst (subst e_12 X_1 X_1prime) X_2 X_2prime) X v))
   (where X_1prime ,(variable-not-in (term ((FreeVars e_11) (FreeVars e_12) (FreeVars v) X)) (term X_1)))
   (where X_2prime ,(variable-not-in (term ((FreeVars e_11) (FreeVars e_12) (FreeVars v) X X_1prime)) (term X_2)))]
  [(subst X X v) v]
  [(subst X_1 X v) X_1]
  [(subst (λ (X T) e) X v) (λ (X T) e)] 
  [(subst (λ (X_1 T) e) X v) 
   (λ (X_1prime T) (subst (subst e X_1 X_1prime) X v))
   (where X_1prime ,(variable-not-in (term ((FreeVars e) (FreeVars v) X)) (term X_1)))]
  [(subst (e_11 e_12) X v) ((subst e_11 X v) (subst e_12 X v))]
  [(subst (! X) X v) (! v)]
  [(subst (! v_1) X v) (! v_1)]
  [(subst (let (! X) = e_11 in e_12) X v) (let (! X) = e_11 in e_12)]
  [(subst (let (! X_1) = e_11 in e_12) X v)
   (let (! X_1prime) = (subst e_11 X v) in (subst (subst e_12 X_1 X_1prime) X v))
   (where X_1prime ,(variable-not-in (term (v (FreeVars e_11) (FreeVars e_12))) (term X_1)))]
  [(subst (dupl e) X v) (dupl (subst e X v))]
  [(subst (drop e) X v) (drop (subst e X v))]
  [(subst (ptr L) X v) (ptr L)]
  [(subst cap X v) cap]
  [(subst (new e) X v) (new (subst e X v))]
  [(subst (free e) X v) (free (subst e X v))]
  [(subst (swap e_1 e_2 e_3) X v) (swap (subst e_1 X v) (subst e_2 X v) (subst e_3 X v))]
  [(subst (Λ P e) X v) 
   (Λ P_prime (subst (substp e P P_prime) X v))
   (where P_prime ,(variable-not-in (term ((FreeLocs e) (FreeLocs v))) (term P)))]
  [(subst (e loc) X v) ((subst e X v) loc)]
  [(subst (loc // e) X v) (loc // (subst e X v))]
  [(subst (let (P // X) = e_1 in e_2) X v)
   (let (P_prime // X) = (subst e_1 X v) in (subst (substp e_2 P P_prime) X v))
   (where (P_prime) ,(variable-not-in (term ((FreeLocs e_2) (FreeLocs v)))))]
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
   (type-alpha-eq? (Ptr L) (Ptr L))]
  [(type-alpha-eq? T_1 T_2)
   -------------------
   (type-alpha-eq? (Cap L T_1) (Cap L T_2))]
  [(where P_3 ,(variable-not-in (term ((FreeLocs T_1) (FreeLocs T_2)))))
   (type-alpha-eq? (substp T_1 P_1 P_3) (substp T_2 P_2 P_3))
   -------------------
   (type-alpha-eq? (∀ P_1 T_1) (∀ P_2 T_2))]
  [(where P_3 ,(variable-not-in (term ((FreeLocs T_1) (FreeLocs T_2)))))
   (type-alpha-eq? (substp T_1 P_1 P_3) (substp T_2 P_2 P_3))
   -------------------
   (type-alpha-eq? (∃ P_1 T_1) (∃ P_2 T_2))])
     
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
  [(where X_31 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term X_11)))
   (where X_32 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term X_12)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst (subst e_12 X_11 X_31) X_12 X_32) 
                     (subst (subst e_22 X_21 X_31) X_22 X_32))
   -------------------
   (alpha-eq? (let (X_11 / X_12) = e_11 in e_12) (let (X_21 / X_22) = e_21 in e_22))]
  [-------------------
   (alpha-eq? X X)]
  [(where X_3 ,(variable-not-in (term ((FreeVars e_1) (FreeVars e_2))) (term X_1)))
   (alpha-eq? (subst e_1 X_1 X_3) (subst e_2 X_2 X_3))
   (type-alpha-eq? T_1 T_2)
   -------------------
   (alpha-eq? (λ (X_1 T_1) e_1) (λ (X_2 T_2) e_2))]
  [(alpha-eq? e_11 e_21) 
   (alpha-eq? e_12 e_22)
   -------------------
   (alpha-eq? (e_11 e_12) (e_21 e_22))]
  [(alpha-eq? v_1 v_2)
   -------------------
   (alpha-eq? (! v_1) (! v_2))]
  [(where X_3 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term X_1)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst e_12 X_1 X_3) (subst e_22 X_2 X_3))
   -------------------
   (alpha-eq? (let (! X_1) = e_11 in e_12) (let (! X_2) = e_21 in e_22))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (dupl e_1) (dupl e_2))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (drop e_1) (drop e_2))]
  [-------------------
   (alpha-eq? (ptr L) (ptr L))]
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
  [(where P_3 ,(variable-not-in (term ((FreeLocs e_1) (FreeLocs e_2))) (term P_1)))
   (alpha-eq? (substp e_1 P_1 P_3) (substp e_2 P_2 P_3))
   -------------------
   (alpha-eq? (Λ P_1 e_1) (Λ P_2 e_2))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (e_1 loc) (e_2 loc))]
  [(alpha-eq? e_1 e_2)
   -------------------
   (alpha-eq? (loc // e_1) (loc // e_2))]
  [(where X_3 ,(variable-not-in (term ((FreeVars e_12) (FreeVars e_22))) (term X_1)))
   (where P_3 ,(variable-not-in (term ((FreeLocs e_12) (FreeLocs e_22))) (term P_1)))
   (alpha-eq? e_11 e_21)
   (alpha-eq? (subst (substp e_12 P_1 P_3) X_1 X_3) (subst (substp e_22 P_2 P_3) X_2 X_3))
   -------------------
   (alpha-eq? (let (P_1 // X_1) = e_11 in e_12) (let (P_2 // X_2) = e_21 in e_22))])

; in order to compare store/expression pairs, I think we are going to have to assume that
; the ith entry of the heap in pair A corresponds to the ith entry of the heap in pair B,
; and then rename the locations of one of the pairs so that the location names match
;(define-judgment-form L3
;  #:mode (alpha-eq-state? I I)
;  #:contract (alpha-eq-state? (store e) (store e))
;  [
;   -------------------
;   (alpha-eq-state? (((l_0 v_0) (l_rest0 v_rest0) ...) e_0) 
;                    (((l_front1 v_front1) ... (l_1 v_1) (l_back1 v_back1) ...) e_1)) 
;   
;  


;(module+ test
;  ;alpha-eq?
;  (test-equal (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in y))) #t)
;  (test-equal (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in x))) #f)
;  (test-equal (judgment-holds (alpha-eq? (let (! x) = (λ (y I) y) in x) (let (! y) = (λ (z I) z) in y))) #t)
;  
;  ;substp
;  (test-equal (term (substp ((Λ p (ptr l_0)) p) p l)) (term ((Λ p (ptr l_0)) l)))
;  
;  
;  )

(define ->L3 
  (reduction-relation 
   L3 
   #:domain (store e)
   (-->
    (store (in-hole E (let * = v in e)))
    (store (in-hole E e))
    let-unit)
   (-->
    (store (in-hole E (let (X_1 / X_2) = (v_1 / v_2) in e)))
    (store (in-hole E (subst (subst e X_1 v_1) X_2 v_2)))
    let-pair)
   (-->
    (store (in-hole E ((λ (X T) e) v)))
    (store (in-hole E (subst e X v)))
    app)
   (-->
    (store (in-hole E (let (! X) = (! v) in e)))
    (store (in-hole E (subst e X v)))
    let-bang)
   (-->
    (store (in-hole E (dupl (! v))))
    (store (in-hole E ((! v) / (! v))))
    dupl)
   (-->
    (store (in-hole E (drop (! v))))
    (store (in-hole E *))
    drop)
   (-->
    (((L_heap v_heap) ...) (in-hole E (new v)))
    (((L_new v) (L_heap v_heap) ...) (in-hole E (L_new // (cap / (! (ptr L_new))))))
    (where L_new ,(variable-not-in (term (L_heap ...)) 'l_1))
    new)
   (-->
    (((L_1 v_1) ... (L_free v_free) (L_2 v_2) ...) (in-hole E (free (L_free // (cap / (! (ptr L_free)))))))
    (((L_1 v_1) ... (L_2 v_2) ...) (in-hole E (L_free // v_free)))
    free)
   (-->
    (((L_1 v_1) ... (L_swap v_swap_out) (L_2 v_2) ...) (in-hole E (swap cap (ptr L_swap) v_swap_in)))
    (((L_1 v_1) ... (L_swap v_swap_in) (L_2 v_2) ...) (in-hole E (cap / v_swap_out)))
    swap)
   (-->
    (store (in-hole E ((Λ P e) L)))
    (store (in-hole E (substp e P L)))
    lapp)
   (-->
    (store (in-hole E (let (P // X) = (L // v) in e)))
    (store (in-hole E (subst (substp e P L) X v)))
    let-lpack)))

  (define f (term (Λ p
    
             (λ (x_c1  (Cap p I)) 
                    (λ (x_xyptrs ((! (Ptr p)) ⊗ (! (Ptr p)))) 
                      (λ (x_v (I -o I)) 
                        (let (x / y) = x_xyptrs in
                          (let (! x_xptr) = x in
                          (let (x_c2 / z) = (swap x_c1 x_xptr x_v) in
                            (x_c2 / (y / z)))))))))))

  
  (define prg1 (term 
                (let (p // x_cptr) = (new *) in 
                  (let (x_cap / x_ptr) = x_cptr in 
                    ((((,f p) x_cap) (dupl x_ptr)) (λ (x I) *))))))
  
   
;(module+ test
;  ;(test-equal (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in x))) #f)
;  (test-equal (term ,(apply-reduction-relation* ->L3 (term (() ,prg1))))
;              (term ((((l_1 (λ (x I) *))) (cap / ((! (ptr l_1)) / *))))))
;  
;  (check-not-false (redex-match L3 e (term (let (p // x_cptr) = (new *) in *))))
;  (check-not-false (redex-match L3 e (term (let (p // x_cptr) = (new *) in (let (x_cap / x_single_ptr) = x_cptr in *)))))
;  (check-not-false (redex-match L3 e (term (let (p // x_cptr) = (new *) in (let (x_cap / x_single_ptr) = x_cptr in (,f p))))))
;  (check-equal? (apply-reduction-relation ->L3 (term (() (let * = * in *)))) (term ((() *))))
;  (check-equal? (apply-reduction-relation ->L3 (term (() (let * = * in (let * = * in *))))) (term ((() (let * = * in *))))))
;   


; another approach to accomplishing this would be to use a judgment form
; this is more efficient, and seems just as readable, if not more so
(define-metafunction L3
  loc-subset : (loc ...) (loc ...) -> boolean
  [(loc-subset (loc_1 ...) (loc_2 ...)) #t
   (where #t ,(subset? (apply set (term (loc_1 ...))) (apply set (term (loc_2 ...)))))]
  [(loc-subset (loc_1 ...) (loc_2 ...)) #f])

;;;THIS WAS A FLAWED IDEA
;;NOTE: this could be done entirely with pattern matching: ((X_0 T_0) ...) ((X_0 T_0) ... (X_1 T_1) (X_2 T_2) (X_3 T_3) ...)
;;the first argument is a type environment directly after 2 bindings were introduced
;;the second argument some legal output type environment for the binding form
;;more concretely, the second argument is a prefix of the first argument which is at 
;;least two entries shorter
;(define-judgement-form L3
;  #:mode (geq2-bindings-removed I I)
;  #:contract (geq2-bindings-removed type-env type-env)
;  [(geq2-bindings-removed ((X_0 T_0) ...) ((X_1 T_1) ...)) 
;   ------------------- (Peel)
;   (geq2-bindings-removed ((X T) (X_0 T_0) ...) ((X T) (X_1 T_1) ...))]
;  
;  [------------------- (Base)
;   (geq2-bindings-removed ((X_0 T_0) (X_1 T_1) (X_2 T_2) ...) ())])
;
;;the first argument is a type environment directly after 1 binding was introduced
;;the second argument some legal output type environment for the binding form
;;more concretely, the second argument is a prefix of the first argument which is at 
;;least one entry shorter
;(define-judgement-form L3
;  #:mode (geq1-binding-removed I I)
;  #:contract (geq1-binding-removed type-env type-env)
;  [(geq1-binding-removed ((X_0 T_0) ...) ((X_1 T_1) ...)) 
;   ------------------- (Peel)
;   (geq1-binding-removed ((X T) (X_0 T_0) ...) ((X T) (X_1 T_1) ...))]
;  [------------------- (Base)
;   (geq1-binding-removed ((X_0 T_0) (X_1 T_1) ...) ())])
  
;TODO: add g1 binding removed judgement
                         
(define-judgment-form L3
  #:mode (L3-type I I I O O)
  #:contract (L3-type loc-env type-env e T type-env)
  [------------------- Unit
   (L3-type loc-env type-env * I type-env)]
  
  [(where #t (loc-subset (type-FreeLocs T) loc-env))
   (where #f ,(member (term X) (term (X_1 ...))))
   ------------------- Var
   (L3-type loc-env ((U_0 X_0 T_0) ... (♭ X T) (U_1 X_1 T_1) ...) X T ((U_0 X_0 T_0) ... (♯ X T) (U_1 X_1 T_1) ...))]
  
  [(L3-type loc-env ((U_env1 X_env1 T_env1) ... (♭ X T_1)) e T_2 ((U_env2 X_env2 T_env2) ... (♯ X T_1)))
   ------------------- Fun
   (L3-type loc-env ((U_env1 X_env1 T_env1) ...) (λ (X T_1) e) (T_1 -o T_2) ((U_env2 X_env2 T_env2) ...))]
  
  [(L3-type loc-env type-env_1 e_1 (T_1 -o T_2) type-env_2)
   (L3-type loc-env type-env_2 e_2 T_1 type-env_3)
   ------------------- App
   (L3-type loc-env type-env_1 (e_1 e_2) T_2 type-env_3)]                    
  
  [(L3-type loc-env type-env_1 e_1 I type-env_2)
   (L3-type loc-env type-env_2 e_2 T type-env_3)
   ------------------- Let-Unit
   (L3-type loc-env type-env_1 (let * = e_1 in e_2) T type-env_3)]                     

  [(L3-type loc-env type-env_1 e_1 T_1 type-env_2)
   (L3-type loc-env type-env_2 e_2 T_2 type-env_3)
   ------------------- Pair
   (L3-type loc-env type-env_1 (e_1 / e_2) (T_1 ⊗ T_2) type-env_3)]
  
  [(L3-type loc-env type-env_1 e_1 (T_11 ⊗ T_12) ((U_env2 X_env2 T_env2) ...))
   (L3-type loc-env ((U_env2 X_env2 T_env2) ... (♭ X_1 T_11) (♭ X_2 T_12)) e_2 T ((U_env3 X_env3 T_env3) ... (♯ X_1 T_11) (♯ X_2 T_12)))
   ------------------- Let-Pair
   (L3-type loc-env type-env_1 (let (X_1 / X_2) = e_1 in e_2) T ((U_env3 X_env3 T_env3) ...))]
                       
        
  
  )
  
(module+ test
  (require rackunit)
  
  ; --- L3-type Unit ---
  
  (check-true (judgment-holds (L3-type (p1 p2) () * I ())))
  ; L3's linear type system does not allow unused entries in the type environment
  (check-false (judgment-holds (L3-type (p1) ((♭ x I)) * I (♭ x I))))
  
  ; --- L3-type Var
  (check-true (judgment-holds (L3-type () ((♭ x I)) x I ((♯ x I)))))
  ; x is removed from the type environment because this is a linear type system
  (check-false (judgment-holds (L3-type (p1 p2 p3) ((♭ x I)) x I ((♭ x I)))))
  ; type references location variable not in location environment
  (check-false (judgment-holds (L3-type (p1 p2 p3) ((♭ x (Ptr p4))) x (Ptr p4) ((♯ x (Ptr p4))))))
  ; adding p4 to location environment fixes this
  (check-true (judgment-holds (L3-type (p1 p2 p3 p4) ((♭ x (Ptr p4))) x (Ptr p4) ((♯ x (Ptr p4))))))
  
  ; --- L3-type Fun
  (check-true (judgment-holds (L3-type () ((♯ x I)) (λ (y (I ⊗ I)) y) ((I ⊗ I) -o (I ⊗ I)) ((♯ x I)))))
  (check-true (judgment-holds (L3-type () ((♯ x I)) (λ (x (I ⊗ I)) x) ((I ⊗ I) -o (I ⊗ I)) ((♯ x I)))))
  (check-true (judgment-holds (L3-type () ((♭ x I)) (λ (x (I ⊗ I)) x) ((I ⊗ I) -o (I ⊗ I)) ((♭ x I)))))
  ; the argument x is not used, so typechecking fails. all variables are linear and therefore must be used.
  (check-false (judgment-holds (L3-type () ((♯ x I)) (λ (x (I ⊗ I)) *) ((I ⊗ I) -o (I ⊗ I)) ((♯ x I)))))
  
  ; --- L3-type App
  (check-true (judgment-holds (L3-type () ((♭ x I)) ((λ (y I) y) x) I ((♯ x I)))))
  
  
  ; --- L3-type Let-Unit ---
  (check-true (judgment-holds (L3-type (p1) ((♭ x I)) (let * = x in *) I ((♯ x I)))))
  ;x cannot be used twice due to linearity
  (check-false (judgment-holds (L3-type (p1) ((♭ x I)) (let * = x in x) I ((♯ x I)))))
  ;x cannot be used because its most recent binding has been used
  (check-false (judgment-holds (L3-type (p1) ((♭ x I) (♯ x I)) (let * = x in *) I ((♯ x I) (♯ x I)))))
  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ x I)) (let * = x in *) I ((♭ x I) (♯ x I)))))
  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ y I)) (let * = x in y) I ((♯ x I) (♯ y I)))))
  
  ;we can use two separate variables
  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ y I)) (let * = x in *) I ((♯ x I) (♭ y I)))))
  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ y (I -o I))) (let * = x in y) (I -o I) ((♯ x I) (♯ y (I -o I))))))
  
  ; --- L3-type Pair ---
  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ y (Ptr p1))) (x / y) (I ⊗ (Ptr p1)) ((♯ x I) (♯ y (Ptr p1))))))
  ; cannot use x after its most recent binding has already been used
  (check-false (judgment-holds (L3-type (p1) ((♭ x I) (♭ x (Ptr p1))) (x / x) (I ⊗ (Ptr p1)) ((♯ x I) (♯ x (Ptr p1))))))
  
  ; --- L3-type Let-Pair ---
  (check-true (judgment-holds (L3-type () ((♭ x I)) (let (x / y) = (* / *) in (let * = x in y)) I ((♭ x I)))))
  
  )

  
  



   ;(-->
   ; (store (let (x_1 / x_2) = (v_1 / v_2) in e))
   ; (store (
    
                      
     
     
     


        
        