;; a ++ [] = a
(assert-not (par (t) (forall ((a (List t)))
  (= (append a constructorNil)
     a))))

;; rev (rev a) = a
(assert-not (par (t) (forall ((a (List t)))
  (= (reverse (reverse a))
     a))))

;; rev (map a b) = map a (rev b)
(assert-not (par (i o) (forall ((a (=> i o)) (b (List i)))
  (= (reverse (map a b))
     (map a (reverse b))))))

;; foldl a (foldl a b c) d = foldl a b (c ++ d)
(assert-not (par (i o) (forall ((a (=> o (=> i o))) (b o) (c (List o)) (d (List i)))
  (= (foldl a (foldl a b c) d)
     (foldl a b (append c d))))))

;; len (rev a) = len a
(assert-not (par (t) (forall ((a (List t)))
  (= (length (reverse a))
     (length a)))))

;; (a ++ b) ++ c = a ++ (b ++ c)
(assert-not (par (t) (forall ((a (List t)) (b (List t)) (c (List t)))
  (= (append (append a b) c)
     (append a (append b c))))))

;; (rev a) ++ (rev b) = rev (b ++ a)
(assert-not (par (t) (forall ((a (List t)) (b (List t)))
  (= (append (reverse a) (reverse b))
     (reverse (append b a))))))

;; (map a b) ++ (map a c) = map a (b ++ c)
(assert-not (par (i o) (forall ((a (=> i o)) (b (List i)) (c (List i)))
  (= (append (map a b) (map a c))
     (map a (append b c))))))

;; foldr a b (foldr a c d) = foldr a (b ++ c) d
(assert-not (par (i o) (forall ((a (=> i (=> o o))) (b (List i)) (c (List i)) (d o))
  (= (foldr a b (foldr a c d))
     (foldr a (append b c) d)))))
