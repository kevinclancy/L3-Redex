#lang racket

(require redex)

(require "l3-lang.rkt" "L3-Redex.rkt")

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


;(redex-match? L3 e lrswap)
;(redex-match? L3 e swapint)
;(traces ->L3 (term (() ,swapint)))
;(judgment-holds (L3-type () () ,lrswap T ()))


;(redex-match? L3 e setx)
;(redex-match? L3 e setxarg)
;(traces ->L3 (term (() ,setxarg)))
;(judgment-holds (L3-type () () ,setxarg T type-env))



(define init4list
  (term
   (λ (x1 Int)
     (λ (x2 Int)
       (λ (x3 Int)
         (λ (x4 Int)
           (let (p0 // xcpd) = (new *) in                   ;; Dummy end node
           (let (p1 // xcp1) = (new (x1 / (p0 // xcpd))) in
           (let (p2 // xcp2) = (new (x2 / (p1 // xcp1))) in
           (let (p3 // xcp3) = (new (x3 / (p2 // xcp2))) in 
           (let (p4 // xcp4) = (new (x4 / (p3 // xcp3))) in ;; create new node pointing to dummy node        
           (p4 // xcp4))))))))))))

(define prueba1
  (term
   (let (pd // xcpd) = (new 3) in                  ;; Dummy end node
   (let (xcd / xpd) = xcpd in
   (pd // (xcd / xpd))))))


(define prueba2
  (term
   (let (pd1 // xcpd1) = (new 3) in                  ;; Dummy end node
   (let (pd2 // xcpd2) = (new 8) in
   ((pd1 // xcpd1) / (pd2 // xcpd2))))))



(define list1
  (term ((((,init4list 42) 63) 108) 1566)))

(define list1-type
  (term
   (∃ p4 ((Cap p4 (Int ⊗ 
   (∃ p3 ((Cap p3 (Int ⊗ 
   (∃ p2 ((Cap p2 (Int ⊗ 
   (∃ p1 ((Cap p1 (Int ⊗ 
   (∃ p0 ((Cap p0 I) ⊗ 
     (!(Ptr p0)))))) ⊗ 
     (!(Ptr p1)))))) ⊗ 
     (!(Ptr p2)))))) ⊗ 
     (!(Ptr p3)))))) ⊗ 
     (!(Ptr p4))))))

(redex-match? L3 T list1-type)


(define first
  (term 
   (λ (x_ref ,list1-type)
     ((,lrswap x_ref) 10) ,list1)))
       


;(redex-match? L3 e prueba2)
;(traces ->L3 (term (() ,prueba2)))
;(judgment-holds (L3-type () () ,prueba2 T type-env))

(redex-match? L3 e first)
(traces ->L3 (term (() ,first)))
;(judgment-holds (L3-type () () ,list1 T type-env))