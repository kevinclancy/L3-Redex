#lang racket
(require redex)
(require racket/set)

(require "l3-lang.rkt" "l3-subst.rkt" "l3-subst-type.rkt")

(provide ->L3 L3-type) 


(define-extended-language L3-rr L3
  ;; Stores
  (store ((L v) ...))

  ;; Evaluation contexts
  (E ::= 
     hole
     (let * = E in e)
     (E / e)
     (v / E)
     (let (X_1 / X_2) = E in e)
     (E e)
     (v E)
     (let (! X) = E in e)
     (dupl E)
     (drop E)
     (new E)
     (free E)
     (swap E e_1 e_2)
     (swap v E e)
     (swap v_1 v_2 E)
     (E L)
     (L // E)
     (let (P // X) = E in e)
     (inl E)
     (inr E)
     (case E of (inl X) => e_l \| (inr X) => e_r)
     (fold [T] E)
     (unfold [T] E)
     ))

(define ->L3 
  (reduction-relation 
   L3-rr 
   #:domain (store e)
   (--> ;; let-unit
    ;; Should this be let * = * ???
    (store (in-hole E (let * = v in e)))
    (store (in-hole E e))
    let-unit)
   (--> ;; let-pair
    (store (in-hole E (let (X_1 / X_2) = (v_1 / v_2) in e)))
    (store (in-hole E (subst (subst e X_1 v_1) X_2 v_2)))
    let-pair)
   (--> ;; app
    (store (in-hole E ((λ (X T) e) v)))
    (store (in-hole E (subst e X v)))
    app)
   (--> ;; let-bang
    (store (in-hole E (let (! X) = (! v) in e)))
    (store (in-hole E (subst e X v)))
    let-bang)
   (--> ;; dupl
    (store (in-hole E (dupl (! v))))
    (store (in-hole E ((! v) / (! v))))
    dupl)
   (--> ;; drop
    (store (in-hole E (drop (! v))))
    (store (in-hole E *))
    drop)
   (--> ;; new 
    (((L_heap v_heap) ...) 
     (in-hole E (new v)))
    (((L_new v) (L_heap v_heap) ...) 
     (in-hole E (L_new // (cap / (! (ptr L_new))))))
    (where L_new ,(variable-not-in (term (L_heap ...)) 'l_1))
    new)
   (--> ;; free
    (((L_1 v_1) ... (L_free v_free) (L_2 v_2) ...) 
     (in-hole E (free (L_free // (cap / (! (ptr L_free)))))))
    (((L_1 v_1) ... (L_2 v_2) ...) 
     (in-hole E (L_free // v_free)))
    free)
   (--> ;; swap
    (((L_1 v_1) ... (L_swap v_swap_out) (L_2 v_2) ...) 
     (in-hole E (swap cap (ptr L_swap) v_swap_in)))
    (((L_1 v_1) ... (L_swap v_swap_in) (L_2 v_2) ...) 
     (in-hole E (cap / v_swap_out)))
    swap)
   (--> ;; lapp
    (store (in-hole E ((Λ P e) L)))
    (store (in-hole E (substp e P L)))
    lapp)
   (--> ;; let-lpack
    (store (in-hole E (let (P // X) = (L // v) in e)))
    (store (in-hole E (subst (substp e P L) X v))) 
    let-lpack)
   (--> ;; case-inl 
    (store (in-hole E (case (inl v as T) of 
                       (inl X_l) => e_l \|
                       (inr X_r) => e_r)))
    (store (in-hole E (subs e_l X_l v)))
    case-inl)
   (--> ;; case-inr 
    (store (in-hole E (case (inr v as T) of 
                        (inl X_l) => e_l \|
                        (inr X_r) => e_r)))
    (store (in-hole E (subs e_r X_r v)))
    case-inr)
   (--> ;; unfld-fld
    (store (in-hole E (unfold [T_1] (fold [T_2] v))))
    (store (in-hole E v))
    unfld-fld)))

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
                  (p // ((((,f p) x_cap) (dupl x_ptr)) (λ (x I) x)))))))
  
   
(module+ test
  (test-equal (judgment-holds (alpha-eq? (let (! x) = * in x) (let (! y) = * in x))) #f)

;  (test-equal (term ,(apply-reduction-relation* ->L3 (term (() ,prg1))))
;              (term ((((l_1 (λ (x I) *))) (cap / ((! (ptr l_1)) / *))))))

  (check-not-false (redex-match L3 e (term (let (p // x_cptr) = (new *) in *))))
  (check-not-false (redex-match L3 e (term (let (p // x_cptr) = (new *) in (let (x_cap / x_single_ptr) = x_cptr in *)))))
  (check-not-false (redex-match L3 e (term (let (p // x_cptr) = (new *) in (let (x_cap / x_single_ptr) = x_cptr in (,f p))))))
  (check-equal? (apply-reduction-relation ->L3 (term (() (let * = * in *)))) (term ((() *))))
  (check-equal? (apply-reduction-relation ->L3 (term (() (let * = * in (let * = * in *))))) (term ((() (let * = * in *))))))


(define-extended-language L3-types L3 
  ;; Mark to keep track of the use of types.
  ;; \flat = ♭ means unused, \sharp = ♯ means used
  (U ::= 
     ♭ ♯) 
  (type-env ::= 
            ((U X T) ...))
  (loc-env  ::= 
            (P ...)))

; another approach to accomplishing this would be to use a judgment form
; this is more efficient, and seems just as readable, if not more so
(define-metafunction L3
  loc-subset : (loc ...) (loc ...) -> boolean
  [(loc-subset (loc_1 ...) (loc_2 ...)) #t
   (where #t ,(subset? (apply set (term (loc_1 ...))) (apply set (term (loc_2 ...)))))]
  [(loc-subset (loc_1 ...) (loc_2 ...)) #f])

; the first argument is the input type environment for type checking a term
; the second argument is the output type environment from type checking the 
; term this function returns a list of all type environment entries which were
; used while typechecking the term; of course, they should all be prefixed by ♯
(define-metafunction L3-types
  used-tenv-entries : type-env type-env -> type-env
  [(used-tenv-entries ((♭ X T) (U_1 X_1 T_1) ...) ((♯ X T) (U_2 X_2 T_2) ...)) 
   ((♯ X T) type-env_rest ...)
   (where (type-env_rest ...) 
          (used-tenv-entries ((U_1 X_1 T_1) ...) ((U_2 X_2 T_2) ...)))]
  [(used-tenv-entries ((♭ X T) (U_1 X_1 T_1) ...) ((♭ X T) (U_2 X_2 T_2) ...)) 
   (used-tenv-entries ((U_1 X_1 T_1) ...) ((U_2 X_2 T_2) ...))]
  [(used-tenv-entries ((♯ X T) (U_1 X_1 T_1) ...) ((♯ X T) (U_2 X_2 T_2) ...)) 
   (used-tenv-entries ((U_1 X_1 T_1) ...) ((U_2 X_2 T_2) ...))]
  [(used-tenv-entries () ()) ()])  

; do all variables in the type environment have ! types?
(define-metafunction L3-types
  tenv-unrestricted : type-env -> boolean
  [(tenv-unrestricted ()) #t]
  [(tenv-unrestricted ((U X (! T)) (U_1 X_1 T_1) ...))
   (tenv-unrestricted ((U_1 X_1 T_1) ...))]
  [(tenv-unrestricted type-env) #f]) 
  
(define-judgment-form L3-types
  #:mode (L3-type I I I O O)
  #:contract (L3-type loc-env type-env e T type-env)
  
  [------------------------------------------------------------------- Unit
   (L3-type loc-env type-env * I type-env)]
  
  [------------------------------------------------------------------- Num
   (L3-type loc-env type-env n Int type-env)]
  
  [(where #t  (loc-subset (type-FLV T) loc-env))
   (where #f ,(member (term X) (term (X_1 ...))))
   ------------------------------------------------------------------- Var
   (L3-type loc-env ((U_0 X_0 T_0) ... (♭ X T) (U_1 X_1 T_1) ...) X 
            T 
            ((U_0 X_0 T_0) ... (♯ X T) (U_1 X_1 T_1) ...))]
   
  [(L3-type loc-env ((U_env1 X_env1 T_env1) ... (♭ X T_1)) e 
            T_2 
            ((U_env2 X_env2 T_env2) ... (♯ X T_1)))
   ------------------------------------------------------------------- Fun
   (L3-type loc-env ((U_env1 X_env1 T_env1) ...) (λ (X T_1) e) 
            (T_1 -o T_2) 
            ((U_env2 X_env2 T_env2) ...))]
  
  [(L3-type loc-env type-env_1 e_1 (T_1 -o T_2) type-env_2)
   (L3-type loc-env type-env_2 e_2 T_1 type-env_3)
   ------------------------------------------------------------------- App
   (L3-type loc-env type-env_1 (e_1 e_2) T_2 type-env_3)]
  
  
  [(L3-type loc-env type-env_1 e T_1 type-env_2)
   ------------------------------------------------------------------- Inl
   (L3-type loc-env type-env_1 (inl e as (T_1 + T_2)) 
            (T_1 + T_2) 
            type-env_2)]

  [(L3-type loc-env type-env_1 e T_2 type-env_2)
   -------------------------------------------------------------------- Inr
   (L3-type loc-env type-env_1 (inr e as (T_1 + T_2)) 
            (T_1 + T_2) 
            type-env_2)]
  
  [ (L3-type loc-env type-env_1 e_c 
             (T_1 + T_2) 
             ((U_env2 X_env2 T_env2) ...))
    (L3-type loc-env ((U_env2 X_env2 T_env2) ... (♭ X_l T_1)) e_l
             T
             ((U_env3 X_env3 T_env3) ... (♯ X_l T_1)))
    (L3-type loc-env ((U_env3 X_env3 T_env3) ... (♭ X_r T_2)) e_r
             T
             ((U_env4 X_env4 T_env4) ... (♯ X_r T_2)))         
   --------------------------------------------------------------------- Case
   (L3-type loc-env type-env_1 (case e_c of (inl X_l) => e_l \| (inr X_r) => e_r)
            T
            ((U_env4 X_env4 T_env4) ...))]


  
  [(L3-type loc-env type-env_1 e_1 I type-env_2)
   (L3-type loc-env type-env_2 e_2 T type-env_3)
   ------------------------------------------------------------------- Let-Unit
   (L3-type loc-env type-env_1 (let * = e_1 in e_2) T type-env_3)]                     

  [(L3-type loc-env type-env_1 e_1 T_1 type-env_2)
   (L3-type loc-env type-env_2 e_2 T_2 type-env_3)
   ------------------------------------------------------------------- Pair
   (L3-type loc-env type-env_1 (e_1 / e_2) (T_1 ⊗ T_2) type-env_3)]
  
  [(L3-type loc-env type-env_1 v T type-env_2)
   (where #t (tenv-unrestricted 
              (used-tenv-entries type-env_1 type-env_2)))
   ------------------------------------------------------------------- Bang
  (L3-type loc-env type-env_1 (! v) (! T) type-env_2)]
  
  [(L3-type loc-env type-env_1 e_1 
            (! T_1) 
            ((U_env2 X_env2 T_env2) ...))
   (L3-type loc-env ((U_env2 X_env2 T_env2) ... (♭ X T_1)) e_2 
            T_2 
            ((U_env3 X_env3 T_env3) ... (♯ X T_1)))
   ------------------------------------------------------------------- Let-Bang
   (L3-type loc-env type-env_1 (let (! X) = e_1 in e_2) 
            T_2 
            ((U_env3 X_env3 T_env3) ...))]
  
  [(L3-type loc-env type-env_1 e 
            (! T) 
            type-env_2)
   ------------------------------------------------------------------- Dupl
   (L3-type loc-env type-env_1 (dupl e) 
            ((! T) ⊗ (! T)) 
            type-env_2)]
  
  [(L3-type loc-env type-env_1 e 
            (! T) 
            type-env_2)
   ------------------------------------------------------------------- Drop
   (L3-type loc-env type-env_1 (drop e) 
            I 
            type-env_2)]
  
  [(L3-type loc-env type-env_1 e T type-env_2)
   (where P ,(variable-not-in (term (type-FLV T)) (term p))) 
   ------------------------------------------------------------------- New
   (L3-type loc-env type-env_1 (new e) 
            (∃ P ((Cap P T) ⊗ (! (Ptr P)))) 
            type-env_2)]
  
  [(L3-type loc-env type-env_1 e 
            (∃ P ((Cap P T) ⊗ (! (Ptr P))) ) 
            type-env_2)
   ------------------------------------------------------------------- Free
   (L3-type loc-env type-env_1 (free e) (∃ P T) type-env_2)]
  
  [(L3-type loc-env type-env_1 e_1 (Cap P T_1) type-env_2)
   (L3-type loc-env type-env_2 e_2 (Ptr P) type-env_3)
   (L3-type loc-env type-env_3 e_3 T_3 type-env_4)
   ------------------------------------------------------------------- Swap
   (L3-type loc-env type-env_1 (swap e_1 e_2 e_3) 
            ((Cap P T_3) ⊗ T_1) 
            type-env_4)]
  
  [(L3-type (P_env ... P) type-env_1 e T type-env_2)
   ------------------------------------------------------------------- LFun
   (L3-type (P_env ...) type-env_1 (Λ P e) (∀ P T) type-env_2)]
  
  [(L3-type (P_env1 ... loc_1 P_env2 ...) type-env_1 e 
            (∀ P_2 T) 
            type-env_2)
   ------------------------------------------------------------------- LApp
   (L3-type (P_env1 ... loc_1 P_env2 ...) type-env_1 (e loc_1) 
            (type-substp T P_2 loc_1) 
            type-env_2)]
  
  [; there is no defined strategy for choosing rho/p in the L3 paper
   ; we need a deterministic strategy that is statically predicatable. 
   ; while this static predicatability isn't necessary for programming 
   ; due to Let-LPack, it is useful for testing
   (L3-type (P_env1 ... P P_env2 ...) type-env_1 e 
            T 
            type-env_2)
   ------------------------------------------------------------------- LPack
   (L3-type (P_env1 ... P P_env2 ...) type-env_1 (P // e) 
            (∃ P T) 
            type-env_2)]
  
  [(L3-type (loc_env ...) type-env_1 e_1 
            (∃ P_prime T_1) 
            ((U_env2 X_env2 T_env2) ...))
   (where T_1prime (type-substp T_1 P_prime P))
   (L3-type (loc_env ... P) ((U_env2 X_env2 T_env2) ... (♭ X T_1prime)) e_2 
            T_2 
            ((U_env3 X_env3 T_env3) ... (♯ X T_1prime)))
   
   (where #f (loc-subset (P) (type-FLV T_2)))
   ------------------------------------------------------------------ Let-LPack
   (L3-type (loc_env ...) type-env_1 (let (P // X) = e_1 in e_2) 
            T_2 
            ((U_env3 X_env3 T_env3) ... ))]
           
  [(L3-type loc-env type-env_1 e_1 
            (T_1 ⊗ T_2) 
            ((U_env2 X_env2 T_env2) ...))
   (L3-type loc-env ((U_env2 X_env2 T_env2) ... (♭ X_1 T_1) (♭ X_2 T_2)) e_2 
            T 
            ((U_env3 X_env3 T_env3) ... (♯ X_1 T_1) (♯ X_2 T_2)))
   ------------------------------------------------------------------- Let-Pair
   (L3-type loc-env type-env_1 (let (X_1 / X_2) = e_1 in e_2) 
            T 
            ((U_env3 X_env3 T_env3) ...))]    
  
  [ (L3-type loc-env type-env_1 e 
             T_subs
             type-env_2)
    (where T_subs (type-subst T tX (μ tX T)))
    ------------------------------------------------------------------- T-Fold
    (L3-type loc-env type-env_1 (fold [(μ tX T)] e) 
             (μ tX T) 
             type-env_2)]
  
  [ (L3-type loc-env type-env_1 e 
             (μ tX T) 
             type-env_2)
    ------------------------------------------------------------------- T-Unfold
    (L3-type loc-env type-env_1 (unfold [(μ tX T)] e) 
             (type-subst T tX (μ tX T)) 
             type-env_2)]
  )
  
(module+ test
  (require rackunit)
  
  
  ;; --- L3-type Unit ---
  (check-true (judgment-holds (L3-type (p1 p2) () * I ())))

  ;; L3's linear type system does not allow unused entries in the 
  ;; type environment
  (check-false (judgment-holds (L3-type (p1) ((♭ x I)) * I (♭ x I))))
  
  ;; --- L3-type Var ---
  
  ;; x is removed from the type environment because this is a linear type
  ;; system
  (check-true (judgment-holds (L3-type () ((♭ x I)) x I ((♯ x I)))))

  ;; type references location variable not in location environment
  (check-false (judgment-holds (L3-type (p1 p2 p3) ((♭ x I)) x 
                                        I ((♭ x I)))))

  (check-false (judgment-holds (L3-type (p1 p2 p3) ((♭ x (Ptr p4))) x 
                                        (Ptr p4) ((♯ x (Ptr p4))))))

  ;; adding p4 to location environment fixes this
  (check-true (judgment-holds (L3-type (p1 p2 p3 p4) ((♭ x (Ptr p4))) x 
                                       (Ptr p4) ((♯ x (Ptr p4))))))
  
  ; --- L3-type Fun
  (check-true (judgment-holds (L3-type () ((♯ x I)) (λ (y (I ⊗ I)) y) 
                                       ((I ⊗ I) -o (I ⊗ I)) ((♯ x I)))))
  
  (check-true (judgment-holds (L3-type () ((♯ x I)) (λ (x (I ⊗ I)) x) 
                                       ((I ⊗ I) -o (I ⊗ I)) ((♯ x I)))))
  
  (check-true (judgment-holds (L3-type () ((♭ x I)) (λ (x (I ⊗ I)) x) 
                                       ((I ⊗ I) -o (I ⊗ I)) ((♭ x I)))))

  ;; The argument x is not used, so typechecking fails. 
  ;; All variables are linear and therefore must be used.
  (check-false (judgment-holds (L3-type () ((♯ x I)) (λ (x (I ⊗ I)) *) 
                                        ((I ⊗ I) -o (I ⊗ I)) ((♯ x I)))))

  ;; --- L3-type App ---

  (check-true (judgment-holds (L3-type () ((♭ x I)) ((λ (y I) y) x) 
                                       I ((♯ x I)))))
  

  ; --- L3-type Let-Unit ---
  (check-true (judgment-holds (L3-type (p1) ((♭ x I)) (let * = x in *) I ((♯ x I)))))
  ;x cannot be used twice due to linearity
  (check-false (judgment-holds (L3-type (p1) ((♭ x I)) (let * = x in x) I ((♯ x I)))))
  ;x cannot be used because its most recent binding has been used
  (check-false (judgment-holds (L3-type (p1) ((♭ x I) (♯ x I)) (let * = x in *) I ((♯ x I) (♯ x I)))))
  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ x I)) (let * = x in *) I ((♭ x I) (♯ x I)))))
  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ y I)) (let * = x in y) I ((♯ x I) (♯ y I)))))

  
  ;; --- L3-type Let-Unit ---  
  (check-true (judgment-holds (L3-type (p1) ((♭ x I)) (let * = x in *) 
                                       I ((♯ x I)))))
  
  ;; x cannot be used twice due to linearity
  (check-false (judgment-holds (L3-type (p1) ((♭ x I)) (let * = x in x) 
                                        I ((♯ x I)))))
  
  ;; x cannot be used because its most recent binding has been used
  (check-false (judgment-holds (L3-type (p1) ((♭ x I) (♯ x I)) (let * = x in *)
                                        I ((♯ x I) (♯ x I)))))

  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ x I)) (let * = x in *) 
                                       I ((♭ x I) (♯ x I)))))

  (check-true (judgment-holds (L3-type (p1) ((♭ x I) (♭ y I)) (let * = x in y) 
                                       I ((♯ x I) (♯ y I)))))
  
  ;; We can use two separate variables
  (check-true (judgment-holds 
               (L3-type (p1) ((♭ x I) (♭ y I)) (let * = x in *) 
                        I ((♯ x I) (♭ y I)))))
  (check-true (judgment-holds 
               (L3-type (p1) ((♭ x I) (♭ y (I -o I))) (let * = x in y) 
                        (I -o I) ((♯ x I) (♯ y (I -o I))))))
  
  ; --- L3-type Pair ---
  (check-true (judgment-holds 
               (L3-type (p1) ((♭ x I) (♭ y (Ptr p1))) (x / y) 
                        (I ⊗ (Ptr p1)) ((♯ x I) (♯ y (Ptr p1))))))

  ;; Cannot use x after its most recent binding has been used
  (check-false (judgment-holds 
                (L3-type (p1) ((♭ x I) (♭ x (Ptr p1))) (x / x) 
                         (I ⊗ (Ptr p1)) ((♯ x I) (♯ x (Ptr p1))))))
  

  ; --- L3-type Let-Pair ---
  (check-true (judgment-holds 
               (L3-type () ((♭ x I)) (let (x / y) = (* / *) in (let * = x in y))
                        I ((♭ x I)))))
  

  ; --- L3-type Bang ---
  (check-true (judgment-holds 
               (L3-type () ((♭ x (! I))) x 
                        (! I) ((♯ x (! I))))))

  (check-true (judgment-holds 
               (L3-type () ((♭ x (! I))) (! (λ (y I) (let * = y in x))) 
                        (! (I -o (! I))) ((♯ x (! I))))))

  ;; Unrestricted values cannot contain linear values
  (check-false (judgment-holds 
                (L3-type () ((♭ x I)) (! (λ (y I) (let * = y in x))) 
                         (! (I -o I)) ((♯ x I)))))


  ;; --- L3-type Dupl ---

  (check-true (judgment-holds 
               (L3-type () () (dupl (! *)) 
                        ((! I) ⊗ (! I)) ())))

  (check-true (judgment-holds 
               (L3-type () ((♭ x (! I))) (dupl x) 
                        ((! I) ⊗ (! I)) ((♯ x (! I))))))
  
  ;; We are prohibited from duplicating linear values
  (check-false (judgment-holds 
                (L3-type () ((♭ x I)) (dupl x) 
                         (I ⊗ I) ((♯ x I)))))
  
  
  ;; --- L3-type Drop ---
  
  ;;We are prohibited from dropping linear values
  (check-false (judgment-holds 
                (L3-type () () (drop *) I ())))

  (check-true (judgment-holds 
               (L3-type () () (drop (! *)) I ())))

  (check-true (judgment-holds 
               (L3-type () ((♭ z (! (∀ p (Ptr p))))) (drop z) 
                        I ((♯ z (! (∀ p (Ptr p))))))))
  
  (check-true (judgment-holds 
               (L3-type () ((♭ z (! (∃ p (Ptr p))))) (drop z) 
                        I ((♯ z (! (∃ p (Ptr p))))))))
  ; --- L3-type Free
  (check-true (judgment-holds (L3-type () () (free (new *)) (∃ p I) ())))
  (check-true (judgment-holds (L3-type () ((♭ x (∃ p ((Cap p I) ⊗ (! (Ptr p)))))) (free x) (∃ p I) ((♯ x (∃ p ((Cap p I) ⊗ (! (Ptr p)))))))))
  
  ; --- L3-type Swap
  (check-true (judgment-holds (L3-type (p) ((♭ x-cap (Cap p I)) (♭ x-ptr (Ptr p))) (swap x-cap x-ptr (λ (x I) x)) ((Cap p (I -o I)) ⊗ I) ((♯ x-cap (Cap p I)) (♯ x-ptr (Ptr p)))))) 

  ; --- L3-type Let-Bang
  (check-true (judgment-holds (L3-type () ((♭ x I)) (let (! x) = (! *) in x) I ((♭ x I)))))
  ; x has been stripped of its unrestrictedness inside let body, so we shouldn't be able to duplicate it
  (check-false (judgment-holds (L3-type () ((♭ y (! I))) (let (! x) = y in (dupl x)) ( (! I) ⊗ (! I) ) ((♯ y (! I))))))
    
  ; Mixed feature tests
  (check-true (judgment-holds (L3-type () () (let (! x) = (! (λ (x I) x)) in (x *)) I ())))
  (check-true (judgment-holds (L3-type () () (let (p // x-cap-ptr) = (new *) in (p // x-cap-ptr)) 
                                             (∃ p ( (Cap p I) ⊗ (! (Ptr p) ) ) ) ())))
  
  (check-true (judgment-holds (L3-type () () (let (p // x-cap-ptr) = (new *) in 
                                             (let (x-cap / x-bang-ptr) = x-cap-ptr in 
                                             (let * = (drop x-bang-ptr) in
                                             (p // x-cap))))
                                       (∃ p (Cap p I) ) ())))
  
  (check-true (judgment-holds (L3-type () () (let (p // x-cap-ptr) = (new *) in 
                                             (let (x-cap / x-bang-ptr) = x-cap-ptr in 
                                             (let (! x-ptr) = x-bang-ptr in 
                                             (let (x / y) = (swap x-cap x-ptr (λ (x I) x)) in 
                                             (let * = y in (p // x))))))
                                       (∃ p (Cap p (I -o I) ) ) ())))

  ; p cannot be a free variable in the type of the body of the lpack binding
  (check-false (judgment-holds (L3-type () () (let (p // x-cap-ptr) = (new *) in 
                                             (let (x-cap / x-bang-ptr) = x-cap-ptr in 
                                             (let (! x-ptr) = x-bang-ptr in 
                                             (let (x / y) = (swap x-cap x-ptr (λ (x I) x)) in 
                                             (let * = y in x)))))
                                       (Cap p (I -o I)) ())))
  
  

  ;; --- L3-type New ---
  (check-true 
   (judgment-holds 
    (L3-type () () (new *) 
             (∃ p ((Cap p I) ⊗ (!(Ptr p)))) ())))
  
  ;; Here we are not checking eq moulo alpha on the returned type. Not a big 
  ;; deal  
  (check-true 
   (judgment-holds 
    (L3-type () () (new (Λ p (λ (x (Ptr p)) x))) 
             (∃ p ((Cap p (∀ p ((Ptr p) -o (Ptr p)))) ⊗ (!(Ptr p)))) ()))) 
  
  ;; --- L3-type Let-Bang ---
  
  (check-true 
   (judgment-holds 
    (L3-type () ((♭ x I)) (let (! x) = (! *) in x) I ((♭ x I)))))

  ;; x has been stripped of its linearity inside let body, 
  ;; so we shouldn't be able to duplicate it
  (check-false 
   (judgment-holds 
    (L3-type () ((♭ y (! I))) (let (! x) = y in (dupl x)) 
             ((! I) ⊗ (! I)) ((♯ y (! I))))))
    
  ;; --- Mixed feature tests ---
  (check-true 
   (judgment-holds 
    (L3-type () () (let (! x) = (! (λ (x I) x)) in (x *)) 
             I ())))


  (check-true 
   (judgment-holds 
    (L3-type () () (let (p // x-cap-ptr) = (new *) in 
                   (p // x-cap-ptr))
             (∃ p ((Cap p I) ⊗ (!(Ptr p)))) 
             ())))

  (check-true 
   (judgment-holds 
    (L3-type () () (let (p // x-cap-ptr) = (new *) in
                   (let (x-cap / x-bang-ptr) = x-cap-ptr in
                   (let * = (drop x-bang-ptr) in
                   (p // x-cap))))
             (∃ p (Cap p I)) 
             ())))

 (check-true 
  (judgment-holds 
   (L3-type () () (let (p // x-cap-ptr) = (new *) in
                  (let (x-cap / x-bang-ptr) = x-cap-ptr in
                  (let (! x-ptr) = x-bang-ptr in
                  (let (x / y) = (swap x-cap x-ptr (λ (x I) x)) in
                  (let * = y in (p // x))))))
            (∃ p (Cap p (I -o I))) 
            ())))

 ; p cannot be a free variable in the type of the body of the lpack binding
 (check-false 
  (judgment-holds 
   (L3-type () () (let (p // x-cap-ptr) = (new *) in
                  (let (x-cap / x-bang-ptr) = x-cap-ptr in
                  (let (! x-ptr) = x-bang-ptr in
                  (let (x / y) = (swap x-cap x-ptr (λ (x I) x)) in
                  (let * = y in x)))))
            (Cap p (I -o I)) 
            ())))
  
  
  
  
  (define lrswap
    (term 
     (λ (xref (∃ p ((Cap p Int) ⊗ (!(Ptr p))))) 
       (λ (x Int)
         (let (p // xcp)   = xref in
         (let (xc0 / xp0) = xcp in         
         (let (xp1 / xp2) = (dupl xp0) in
         (let (! xp4)      = xp2 in 
         (let (xc1 / y)    = (swap xc0 xp4 x) in
         ((p // (xc1 / xp1)) / y))))))))))  
      
  ;; Apply lrswap to change an integer value stored in memory.
  (define swapint
    (term 
     (let (ploc // xpck) = (new 5) in
       ((,lrswap (ploc // xpck)) 10))))
     
  
  (redex-match? L3 e lrswap)
  (redex-match? L3 e swapint)
  
  (traces ->L3 (term (() ,swapint)))   
  
;  (build-derivations (L3-type () () ,lrswap T ()))






  
  )
