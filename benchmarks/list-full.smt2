; Lists with Nil, Cons, append, reverse, length, map, foldl and foldr; various
; combinations of these have been used to test HipSpec
(declare-datatypes (a)
  ((List (Nil) (Cons (head a) (tail (List a))))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))

(define-fun-rec
  (par (a)
    (append
       ((x (List a)) (y (List a))) (List a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun-rec
  (par (a)
    (reverse
       ((x (List a))) (List a)
       (match x
         (case Nil (as Nil (List a)))
         (case (Cons z xs) (append (reverse xs) (Cons z (as Nil (List a)))))))))
(define-fun-rec
  (par (a)
    (length
       ((x (List a))) (Nat)
       (match x
         (case Nil Z)
         (case (Cons z xs) (S (length xs)))))))
(define-fun-rec
  (par (a b)
    (map
       ((x (=> a b)) (y (List a))) (List b)
       (match y
         (case Nil (as Nil (List b)))
         (case (Cons z xs) (as (Cons (@ x z) (map x xs)) (List b)))))))
(define-fun-rec
  (par (a b)
    (foldl
       ((f (=> b (=> a b))) (x b) (y (List a))) b
       (match y
         (case Nil x)
         (case (Cons z xs) (foldl f (@ (@ f x) z) xs))))))
(define-fun-rec
  (par (a b)
    (foldr
       ((f (=> a (=> b b))) (y (List a)) (x b)) b
       (match y
         (case Nil x)
         (case (Cons h t) (@ (@ f h) (foldr f t x)))))))
(check-sat)
