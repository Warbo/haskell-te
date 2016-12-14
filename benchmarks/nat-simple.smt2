; Natural numbers
(declare-datatypes () ((Nat (Z) (S (p Nat)))))

; Functions equivalent to the constructors
(define-fun constructor-Z () Nat
  (as Z Nat))

(define-fun constructor-S ((local-p Nat)) Nat
  (as (S local-p) Nat))

; Functions equivalent to the destructors
(define-fun destructor-p ((local-x Nat)) Nat
  (match local-x
    (case (S local-p) (as local-p Nat))))

; Arithmetic functions
(define-fun-rec
  plus
    ((x Nat) (y Nat)) Nat
    (match x
      (case  Z      y)
      (case (S x2) (S (plus x2 y)))))
      
(define-fun-rec
  times
    ((x Nat) (y Nat)) Nat
    (match x
      (case  Z      Z)
      (case (S x2) (plus y (times x2 y)))))

(check-sat)
