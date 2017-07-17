;; a + 0 = a
(assert-not (forall ((a Nat))
  (= (plus a constructorZ)
     a)))

;; a * 0 = 0
(assert-not (forall ((a Nat))
  (= (times a constructorZ)
     constructorZ)))

;; a + b = b + a
(assert-not (forall ((a Nat) (b Nat))
  (= (plus a b)
     (plus b a))))

;; (a + b) + c = a + (b + c)
(assert-not (forall ((a Nat) (b Nat) (c Nat))
  (= (plus (plus a b) c)
     (plus a (plus b c)))))

;; (a * b) + (c * b) = (a + c) * b
(assert-not (forall ((a Nat) (b Nat) (c Nat))
  (= (plus (times a b) (times c b))
     (times (plus a c) b))))

;; a + (S b) = S (a + b)
(assert-not (forall ((a Nat) (b Nat))
  (= (plus a (constructorS b))
     (constructorS (plus a b)))))

;; a * (S b) = a + (a * b)
(assert-not (forall ((a Nat) (b Nat))
  (= (times a (constructorS b))
     (plus a (times a b)))))

;; a * b = b * a
(assert-not (forall ((a Nat) (b Nat))
  (= (times a b)
     (times b a))))

;; (a * b) * c = a * (b * c)
(assert-not (forall ((a Nat) (b Nat) (c Nat))
  (= (times (times a b) c)
     (times a (times b c)))))

;; (a * b) + (a * c) = (b + c) * a
(assert-not (forall ((a Nat) (b Nat) (c Nat))
  (= (plus (times a b) (times a c))
     (times (plus b c) a))))

;; (S m) + n = m + (S n)
(assert-not (forall ((n Nat) (m Nat))
  (= (plus (constructorS m) n)
     (plus m (constructorS n)))))

;; x + (y + z) = y + (x + z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (plus x (plus y z))
     (plus y (plus x z)))))
