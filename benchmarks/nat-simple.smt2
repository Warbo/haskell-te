; Natural numbers
(declare-datatypes () ((Nat (Z) (S (p Nat)))))

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
