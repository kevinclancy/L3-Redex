#lang racket

(require redex)

(require "l3-lang.rkt" "L3-Redex.rkt")


;; Some small problems from L3 paper.

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
;(traces ->L3 (term (() ,swapint)))
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
;(traces ->L3 (term (() ,setxarg)))
;  (check-true (judgment-holds (L3-type () () ,setxarg T type-env)))
)


;; Iterative definition of a list.
;; Too complicated to handle because of types...
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



;; Definition of recursive lists

(define NatList
  (term
   (μ α (I + (Int ⊗ (∃ p ((Cap p α) ⊗ (! (Ptr p)))))))))

(define NLBody
  (term
   (I + (Int ⊗ (∃ p ((Cap p ,NatList) ⊗ (! (Ptr p))))))))


(define nil
  (term
   (fold [,NatList]
         (inl * as ,NLBody))))

(define cons
  (term
   (λ (x_n Int)
     (λ (x_list ,NatList)
       (fold [,NatList]
             (inr (x_n / (new x_list)) as ,NLBody))))))


(define l1
  (term 
   ((,cons 8) ((,cons 3) ,nil))))
       

#|
(define length
  (term
   (λ (x_list ,NatList)
     (case (unfold [,NatList] x_list) of
       (inl x_l) => (let * = x_l in 0) \| 
       (inr x_r) => (1 + (length x_r))))))

|#


;; Takes a list and returns a pair with its components.
(define split
  (term
   (λ (x_list (Int ⊗ (∃ p ((Cap p ,NatList) ⊗ (! (Ptr p))))))
     (let (x_i / x_epkg) = x_list in
     (let (p // x_next) = (free x_epkg) in
     (x_i / x_next))))))
       

(module+ test
 
  (check-true (redex-match? L3 T NatList))
  (check-true (redex-match? L3 T NLBody))
  (check-true (redex-match? L3 e nil))
  (check-true (redex-match? L3 e cons))
  (check-true (redex-match? L3 e l1))
  
  (check-true (judgment-holds (L3-type () () ,nil T type-env)))
  (check-true (judgment-holds (L3-type () () ,cons T type-env)))
  (check-true (judgment-holds (L3-type () () ,l1 T type-env)))
  (check-true (judgment-holds (L3-type () () ,split T type-env)))
  
)
