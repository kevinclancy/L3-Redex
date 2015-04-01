#lang racket

(require redex)

(provide L3)

(define-language L3
  ;expressions
  (e ::= 
     *                             ;; unit
     n                             ;; numbers
     (let * = e in e)              ;; unit elimination 
     (e / e)                       ;; pair
     (let (X / X) = e in e)        ;; pair elimination
     X                             ;; variable
     (λ (X T) e)                   ;; abstraction
     (e e)                         ;; application
     (! v)                         ;; unrestricted value
     (let (! X) = e in e)          ;;  
     (dupl e)                      ;; duplicate !-type
     (drop e)                      ;; eliminate !-type
     (ptr L)                       ;; pointer to a location
     cap                           ;; capability to a a location
     (new e)                     ;; allocate mutable reference
     (free e)                      ;; deallocate mutable reference
     (swap e e e)                  ;; deference and update mutable reference  
     (Λ P e)                       ;; intro universal abstraction on location 
     (e loc)                       ;; elim universal abstraction on location
     (loc // e)                    ;; intro existential abstraction on location 
     (let (P // X) = e in e)      ;; elim existential abstraction on location
     ;; Sum type extensions
     (inl e as T)
     (inr e as T)
     (case e_c of (inl X) => e_l \| (inr X) => e_r)
     ;; Recursive types extension
     (fold [T] e)
     (unfold [T] e))
     

  ;term variable
  (X ::= 
     x y z (variable-prefix x) (variable-prefix y) (variable-prefix z)) 
  ;location constant or variable
  (loc ::= 
       L P) 
  ;location constant
  (L ::= 
     l m n (variable-prefix l) (variable-prefix m) (variable-prefix n)) 
  ;location variable
  (P ::= 
     p q r (variable-prefix p) (variable-prefix q) (variable-prefix r))
  
  (tX ::=
      α β γ (variable-prefix α) (variable-prefix β) (variable-prefix γ))
  
  
  ;values
  (v ::= 
     *
     n
     (v / v)
     X
     (λ (X T) e)
     (! v)
     (ptr L)
     cap
     (Λ P e)
     (loc // v)
     ;; Sum type extensions
     (inl v as T)
     (inr v as T)
     ;; Recursive type extension
     (fold [T] v))
  (n ::=
     number)
  ;types
  (T ::=
     tX           ;; Type variable
     I            ;; unit
     Int          ;; numbers
     (T ⊗ T)      ;; tensor product. \otimes + alt-\ gives ⊗
     (T + T)      ;; Sum type     
     (μ tX T)     ;; Recursive type
     (T -o T)     ;; linear function
     (! T)        ;; unrestricted "of course" type
     (Ptr loc)    ;; type of pointer to location w
     (Cap loc T)  ;; capability for location, where the stored value has type T
     (∀ P T)      ;; universal location abstraction 
     (∃ P T))     ;; existential location abstraction
 ) 
 