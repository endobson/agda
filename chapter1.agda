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
ex1-2 {a} {b} {c} g1 g2 = g8
  where
  g1' : GCD' (abs' a) (abs' b) 1
  g1' = (gcd->gcd' g1)
  g2' : GCD' (abs' a) (abs' c) 1
  g2' = (gcd->gcd' g2)
  g3 : GCD' (abs' a) (abs' b *' abs' c) 1
  g3 = (ex1-2' g1' g2')
  g4 : GCD (int (abs' a)) (int (abs' b *' abs' c)) (int 1)
  g4 = (gcd'->gcd/nat g3)
  g5 : GCD (abs a) (int (abs' b) * (int (abs' c))) (int 1)
  g5 rewrite (sym (int-inject-*' {abs' b} {abs' c}))
    = g4
  g6 : GCD (abs a) (abs b * abs c) (int 1)
  g6 = g5
  g7 : GCD (abs a) (abs (b * c)) (int 1)
  g7 rewrite (abs-inject-* {b} {c})
    = g6
  g8 : GCD a (b * c) (int 1)
  g8 = (gcd-remove-abs (gcd-sym (gcd-remove-abs (gcd-sym g7))))
  


