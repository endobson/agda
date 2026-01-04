{-# OPTIONS --cubical --safe --exact-split #-}

module prime-div-count.computational where

open import additive-group.instances.nat
open import base
open import div
open import equality
open import gcd.computational
open import lcm.exists
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.minmax
open import order.minmax.instances.nat
open import prime
open import prime-div-count
open import semiring.exponentiation
open import semiring.instances.nat
open import sigma.base

prime-div-count : Prime' -> Nat⁺ -> Nat
prime-div-count p a = fst (compute-prime-div-count p a)
prime-div-count-proof : (p : Prime') -> (a : Nat⁺) -> PrimeDivCount p ⟨ a ⟩ (prime-div-count p a)
prime-div-count-proof p a = snd (compute-prime-div-count p a)

*'-prime-div-count⁺ : (p : Prime') (a b : Nat⁺)
  -> prime-div-count p (a *⁺ b) == prime-div-count p a +' prime-div-count p b
*'-prime-div-count⁺ p a b =
  prime-div-count-unique
    (prime-div-count-proof p (a *⁺ b))
    (*'-prime-div-count (prime-div-count-proof p a) (prime-div-count-proof p b))

div-prime-div-count : {a b : Nat⁺} -> a div⁺ b -> (p : Prime')
                      -> prime-div-count p a ≤ prime-div-count p b
div-prime-div-count {a} {b} a%b p =
  PrimeDivCount.upper-bound
    (prime-div-count-proof p b)
    (prime-div-count p a)
    (div'-trans (PrimeDivCount.%a (prime-div-count-proof p a)) a%b)

zero-prime-div-count : {a : Nat⁺} -> (p : Prime') -> ¬ (⟨ p ⟩ div' ⟨ a ⟩) -> prime-div-count p a == 0
zero-prime-div-count {a} p d =
  prime-div-count-unique (prime-div-count-proof p a) (¬div-prime-div-count d)

suc-prime-div-count : {a : Nat⁺} -> (p : Prime') -> (d : ⟨ p ⟩ div' ⟨ a ⟩)
                      -> prime-div-count p a ==
                         suc (prime-div-count p (div⁺->multiple⁺ {Prime'.nat⁺ p} {a} d))
suc-prime-div-count {a} p d = prime-div-count-unique (prime-div-count-proof p a) pa
  where
  r = (div⁺->multiple⁺ {Prime'.nat⁺ p} {a} d)
  r' = ⟨ r ⟩
  pr : PrimeDivCount p r' (prime-div-count p r)
  pr = prime-div-count-proof p r

  pr' : PrimeDivCount p (⟨ p ⟩ *' r') (suc (prime-div-count p r))
  pr' = prime-div-count-suc pr

  path : ⟨ p ⟩ *' r' == ⟨ a ⟩
  path = *'-commute {⟨ p ⟩} {r'} >=> snd d

  pa : PrimeDivCount p ⟨ a ⟩ (suc (prime-div-count p r))
  pa = transport (\i -> PrimeDivCount p (path i) (suc (prime-div-count p r))) pr'


prime-div-count->prime-power-div : (p : Prime') -> (a : Nat⁺)
                                   -> (prime-power p (prime-div-count p a)) div' ⟨ a ⟩
prime-div-count->prime-power-div p a = PrimeDivCount.%a (prime-div-count-proof p a)

prime-div-count->prime-div : (p : Prime') (a : Nat⁺)
                             -> prime-div-count p a > 0
                             -> ⟨ p ⟩ div' ⟨ a ⟩
prime-div-count->prime-div p a (x , path) =
  div'-trans (prime-power-div p dc⁺) (prime-div-count->prime-power-div p a)
  where
  full-path : suc x == prime-div-count p a
  full-path = cong suc (sym +'-right-zero) >=> sym +'-right-suc >=> path
  dc⁺ : Nat⁺
  dc⁺ = prime-div-count p a , transport (cong Pos' full-path) tt


prime-div->prime-div-count : (p : Prime') (a : Nat⁺)
                             -> ⟨ p ⟩ div' ⟨ a ⟩
                             -> prime-div-count p a > 0
prime-div->prime-div-count p a d@(x , path) =
  prime-div-count p (x , (div'-pos->pos' d (snd a))) ,
  +'-right
    (prime-div-count-unique
      (subst (\x -> PrimeDivCount p x 1) ^ℕ-one (prime-power-div-count p 1))
      (prime-div-count-proof p (Prime'.nat⁺ p))) >=>
  sym (*'-prime-div-count⁺ p (x , (div'-pos->pos' d (snd a))) (Prime'.nat⁺ p))
  >=> cong (prime-div-count p) (ΣProp-path isPropPos' path)



gcd-prime-div-count⁺ : (p : Prime') (a b : Nat⁺)
  -> prime-div-count p (gcd⁺ a b) == min (prime-div-count p a) (prime-div-count p b)
gcd-prime-div-count⁺ p a b =
  prime-div-count-unique
    (prime-div-count-proof p (gcd⁺ a b))
    (gcd-prime-div-count (gcd⁺-proof a b) p (prime-div-count-proof p a) (prime-div-count-proof p b))

lcm-prime-div-count⁺ : (p : Prime') (a b : Nat⁺)
  -> prime-div-count p (lcm⁺ a b) == max (prime-div-count p a) (prime-div-count p b)
lcm-prime-div-count⁺ p a b =
  (prime-div-count-unique
    (prime-div-count-proof p (lcm⁺ a b))
    (lcm-prime-div-count (lcm⁺-proof a b) p (prime-div-count-proof p a) (prime-div-count-proof p b)))
