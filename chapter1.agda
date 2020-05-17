module chapter1 where

open import equality
open import abs
open import nat
open import int
open import div
open import prime
open import gcd

ex1-1 : {a b c d : Int} -> GCD a b (int 1) -> c div a -> d div b -> GCD c d (int 1)
ex1-1 {a} {b} {c} {d} (gcd a b _ _ _ _ gcd-f) c-div-a d-div-b = 
  gcd c d (int 1) tt div-one div-one 
  (\x x-div-c x-div-d -> 
    (gcd-f x (div-trans x-div-c c-div-a) (div-trans x-div-d d-div-b)))

ex1-2' : {a b c : Nat} -> GCD' a b 1 -> GCD' a c 1 -> GCD' a (b *' c) 1
ex1-2' (gcd' a@(suc _) b@(suc _) _ _ _ f-b) (gcd' a@(suc _) c@(suc _) _ _ _ f-c) = 
  prime-gcd' a (b *' c) f
  where
  ¬prime-div-one : {p : Nat} -> Prime' p -> ¬(p div' 1)
  ¬prime-div-one p p%1 with div'->≤ p%1
  ...                     | zero-≤ = 0-is-¬prime p
  ...                     | (inc-≤ zero-≤) = 1-is-¬prime p

  f : {p : Nat} -> (Prime' p) -> p div' a -> p div' (b *' c) -> Bot
  f {p'} p p%a p%bc with (prime-divides-a-factor p {b} {c} p%bc)
  ... | inj-l p%b = ¬prime-div-one p (f-b p' p%a p%b)
  ... | inj-r p%c = ¬prime-div-one p (f-c p' p%a p%c)
ex1-2' g@(gcd' a zero _ _ _ _) _ = g
ex1-2' {a} {b} _ g@(gcd' a zero _ _ _ _) rewrite (*'-commute {b} {zero}) = g
ex1-2' {zero} b@{suc _} c@{suc _} gb gc
  with gcd'-zero->id gb | gcd'-zero->id gc
... | refl | refl = gb

ex1-2 : {a b c : Int} -> GCD a b (int 1) -> GCD a c (int 1)
                      -> GCD a (b * c) (int 1)
ex1-2 {a} {b} {c} g1 g2 = g7
  where
  g1' : GCD' (abs' a) (abs' b) 1
  g1' = (gcd->gcd' g1)
  g2' : GCD' (abs' a) (abs' c) 1
  g2' = (gcd->gcd' g2)
  g3 : GCD' (abs' a) (abs' b *' abs' c) 1
  g3 = (ex1-2' g1' g2')
  g4 : GCD (abs a) (int (abs' b *' abs' c)) (int 1)
  g4 = (gcd'->gcd/nat g3)
  g5 : GCD (abs a) (abs b * abs c) (int 1)
  g5 rewrite (sym (int-inject-*' {abs' b} {abs' c}))
    = g4
  g6 : GCD (abs a) (abs (b * c)) (int 1)
  g6 rewrite (abs-inject-* {b} {c})
    = g5
  g7 : GCD a (b * c) (int 1)
  g7 = (gcd-remove-abs (gcd-sym (gcd-remove-abs (gcd-sym g6))))

RPrime : Int -> Int -> Set
RPrime a b = GCD a b (int 1)

rp-* : {a b c : Int} -> RPrime b a -> RPrime c a -> RPrime (b * c) a
rp-* rp1 rp2 = gcd-sym (ex1-2 (gcd-sym rp1) (gcd-sym rp2))
  
rp-^ : {a b : Int} -> RPrime a b -> (n : Nat) -> {Pos' n} -> RPrime (a ^ n) b
rp-^ {a} rp (suc (zero)) rewrite (^-right-one {a}) = rp
rp-^ rp (suc (suc n)) = rp-* rp (rp-^ rp (suc n))

rp-sym : {a b : Int} -> RPrime a b -> RPrime b a
rp-sym = gcd-sym


ex1-3 : {a b : Int} -> (RPrime a b)
         -> (n k : Nat) -> {Pos' n} -> {Pos' k} -> RPrime (a ^ n) (b ^ k)
ex1-3 rp n k {pos-n} {pos-k} = (rp-sym (rp-^ (rp-sym (rp-^ rp n {pos-n})) k {pos-k}))




