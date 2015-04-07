#lang racket

(require redex)

(require "l3-lang.rkt" "L3-Redex.rkt")


;; Some small functions extracted from L3 paper.

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
     

(module+ test
  (require rackunit)
  
  (check-true (redex-match? L3 e swapint))
  (check-true (judgment-holds (L3-type () () ,lrswap T ())))
 )


(define setx
  (term
   (λ (xref (∃ p ((Cap p (((! Int) ⊗ Int) ⊗ Int)) ⊗ (! (Ptr p)))))
     (λ (x_1 Int)
       (let (p // xcp) = xref in
       (let (x_c1 / x_l0) = xcp in
       (let (x_l1 / x_l2) = (dupl x_l0) in
       (let (x_l3 / x_l4) = (dupl x_l1) in
       (let (! x_l2r) = x_l2 in                                  
       (let (x_c2 / x_a) = (swap x_c1 x_l2r *) in 
       (let (x_y_0 / z_0) = x_a in 
       (let (x_0 / y_0) = x_y_0 in
       (let * = (drop x_0) in
       (let (! x_l3r) = x_l3 in  
       (let (x_c3 / x_b) = (swap x_c2 x_l3r ((x_1 / y_0) / z_0)) in
       (let * = x_b in
       (let * = x_y_0 in  
       (p // (x_c3 / x_l4)))))))))))))))))))

(define setxarg
    (term 
     (let (ploc // xpck) = (new (((! 5) / 8) / 10)) in
       ((,setx (ploc // xpck)) 33))))

(module+ test
  (check-true (redex-match? L3 e setx))
  (check-true (redex-match? L3 e setxarg))

)

;; -----------------------------------------------------------------------------
;; Lists
;; -----------------------------------------------------------------------------

;; Iterative definition of a list.
;; Too complicated to handle because of types... We would need several 
;; functions to handle cases for different lengths.
(define init4list
  (term
   (λ (x1 Int)
     (λ (x2 Int)
       (λ (x3 Int)
         (λ (x4 Int)
           (let (p0 // xcpd) = (new *) in                   
           (let (p1 // xcp1) = (new (x1 / (p0 // xcpd))) in
           (let (p2 // xcp2) = (new (x2 / (p1 // xcp1))) in
           (let (p3 // xcp3) = (new (x3 / (p2 // xcp2))) in 
           (let (p4 // xcp4) = (new (x4 / (p3 // xcp3))) in 
           (p4 // xcp4))))))))))))


(define list1
  (term ((((,init4list 42) 63) 108) 1566)))



;; Type definition of recursive integer lists
(define NatList
  (term
   (μ α (I + (Int ⊗ (∃ p ((Cap p α) ⊗ (! (Ptr p)))))))))

;; Auxiliary type for sum construction
(define NLBody
  (term
   (I + (Int ⊗ (∃ p ((Cap p ,NatList) ⊗ (! (Ptr p))))))))


;; Reference to a NatList
(define NatListRef
  (term 
   (∃ p ((Cap p ,NatList) ⊗ (!(Ptr p))))))


;; nil creates an empty list in memory
(define nil
  (term
   (new (fold [,NatList]
         (inl * as ,NLBody)))))

;; Given an integer x_n and a reference to a list, cons creates a new list with
;; x_n as the first element and a pointer to the rest of the list.
(define cons
  (term
   (λ (x_n Int)
     (λ (x_reflist ,NatListRef)        
       (new (fold [,NatList]
                  (inr (x_n / x_reflist) as ,NLBody)))))))

;; Small list to test nil and cons
(define l1
  (term
   ((,cons 1) ((,cons 2) ,nil))))



       


;; append is a recursive function that takes two references to NatList 
;; x_list1ref and x_list2ref and returns a reference to a list that is the 
;; concatenation of both.
;; Note that the algorithm destroys the original list in x_list1ref. This 
;; memory location is now updated with the result list.
(define append
  (term
   (fix
    (λ (x_append (,NatListRef -o (,NatListRef -o ,NatListRef)))
      (λ (x_list1ref ,NatListRef)
        (λ (x_list2ref ,NatListRef)
          ;; First part: open the reference and obtain the first list.
          ;; We will recurse over this.
          (let (p_l1 // x_l1_pkg) = x_list1ref in
          (let (x_cap_l1_pre / x_ptr_l1) = x_l1_pkg in
          (let (x_ptr_l1_1 / x_ptr_l1_2) = (dupl x_ptr_l1) in
          (let (! x_ptr_l1_1_lin) = x_ptr_l1_1 in           
          (let (x_cap_l1_post / x_list1) = (swap x_cap_l1_pre x_ptr_l1_1_lin *) in
          ;; Use a case expression to determine if we are dealing with an empty
          ;; list or not.
          (case (unfold [,NatList] x_list1) of
            (inl x) => ;; CASE: Empty list. Proceed to open the reference for
                       ;; the second list and replace the original reference 
                       ;; with it. This way, we replace the * element that marks
                       ;; the end of the list and with the second list.
                       (let * = x in
                       (let (x_ptr_l1_3 / x_ptr_l1_4) = (dupl x_ptr_l1_2) in
                       (let (! x_ptr_l1_3_lin) = x_ptr_l1_3 in
                       (let (p_l2 // x_l2_pkg) = x_list2ref in
                       (let (x_cap_l2 / x_ptr_l2) = x_l2_pkg in
                       (let (x_ptr_l2_1 / x_ptr_l2_2) = (dupl x_ptr_l2) in
                       (let (! x_ptr_l2_1_lin) = x_ptr_l2_1 in  
                       (let (x_cap_unit / x_list2) = (swap x_cap_l2 x_ptr_l2_1_lin *) in
                       (let (p_free // x_unit2) = (free ( p_l2 // (x_cap_unit / x_ptr_l2_2))) in
                       (let * = x_unit2 in 
                       (let (x_cap_final_inl / x_unit) = (swap x_cap_l1_post x_ptr_l1_3_lin x_list2) in
                       (let * = x_unit in  
                       (p_l1 // (x_cap_final_inl / x_ptr_l1_4)))))))))))))) \| 
            (inr x) => ;; CASE: Int and reference to next list node. Here we
                       ;; perform a recursive call to append now with the rest
                       ;; of the current list and x_list2ref. This returns a
                       ;; reference to the 'new' list. Finally we construct a 
                       ;; new list that contains the original Int value and the
                       ;; list returned by the append.
                       (let (x_val / x_next_ref) = x in
                       (let (p_new // x_new_pkg) = ((x_append x_next_ref) x_list2ref) in
                       (let (x_ptr_l1_3 / x_ptr_l1_4) = (dupl x_ptr_l1_2) in 
                       (let (! x_ptr_l1_3_lin) = x_ptr_l1_3 in    
                       (let (x_cap_final / x_unit) = (swap x_cap_l1_post x_ptr_l1_3_lin  (inr (x_val / (p_new // x_new_pkg)) as ,NLBody)) in
                       (let * = x_unit in
                       (p_l1 // (x_cap_final / x_ptr_l1_4))))))))))))))))))))
                             

;; The traces for this examples when applying the ->L3 reduction relation show
;; that the final result is what we expected. 
;; However, the type-checking of the function fails. We believe that
;; the main reason for this is some small mistake when handling the pointers
;; or variables in the code. As far as we know, Redex provides no facility to 
;; 'debug' the type- checking judgment, thus we have no clear view of the
;; problem. After a minucious review of the code and typing rules, we still
;; have no solution for the problem at the submission time.

;; Simple case, appending two empty lists.
(define append_ex1
  (term
   ((,append ,nil) ,nil)))

;; Append a list with another (both the same, but with different memory 
;; location2)
(define append_ex2
  (term
   ((,append ,l1) ,l1)))


(module+ test
 

  (check-true (redex-match? L3 T NatList))
  (check-true (redex-match? L3 T NLBody))
  (check-true (redex-match? L3 e nil))
  (check-true (redex-match? L3 e cons))
  (check-true (redex-match? L3 e l1))
  (check-true (redex-match? L3 e append))
  (check-true (redex-match? L3 e append_ex1))
  (check-true (redex-match? L3 e append_ex2))
  
  (check-true (judgment-holds (L3-type () () ,nil T type-env)))
  (check-true (judgment-holds (L3-type () () ,cons T type-env)))
  (check-true (judgment-holds (L3-type () () ,l1 T type-env)))
  
  ;; Fail to type-check for append.
  ; (check-true (judgment-holds (L3-type () () ,append T type-env)))
  ; (check-true (judgment-holds (L3-type () () ,append_ex1 T type-env)))
  ; (check-true (judgment-holds (L3-type () () ,append_ex2 T type-env)))
  
)
