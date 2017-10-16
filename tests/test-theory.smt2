; Simple theory of pairs (cartesian products), meant to be explored quickly
(declare-datatypes (a)
  ((Pair (MkPair (fst a) (snd a)))))

; Functions equivalent to the constructors
(define-fun
  (par (a)
    (constructor-MkPair ((local-fst a) (local-snd a)) (Pair a)
      (as (MkPair local-fst local-snd) (Pair a)))))

; Functions equivalent to the destructors
(define-fun
  (par (a)
    (destructor-fst ((local-x (Pair a))) a
      (match local-x
        (case (MkPair local-y local-z) local-y)))))

(define-fun
  (par (a)
    (destructor-snd ((local-x (Pair a))) a
      (match local-x
        (case (MkPair local-y local-z) local-z)))))

; Other functions
(define-fun
  (par (a)
    (swap
       ((x (Pair a))) (Pair a)
       (MkPair (destructor-snd x) (destructor-fst x)))))

(define-fun
  (par (a)
    (map
       ((f (=> a a)) (x (Pair a))) (Pair a)
       (MkPair (@ f (destructor-fst x)) (@ f (destructor-snd x))))))

(define-fun
  (par (a)
    (uncurry
       ((f (=> a (=> a a))) (x (Pair a))) a
       (@ (@ f (destructor-fst x)) (destructor-snd x)))))


(check-sat)
