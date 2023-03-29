{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module prime-gcd where

open import additive-group
open import additive-group.instances.int
open import base
open import div
open import equality
open import gcd.euclidean-algorithm
open import gcd.propositional
open import int
open import lcm
open import nat
open import nat.order
open import prime
open import relation
open import relatively-prime
open import ring
open import ring.implementations.int
open import semiring

private
  RP = RelativelyPrime⁰

relatively-prime->gcd : {a b : Nat} -> RP a b -> GCD' a b 1
relatively-prime->gcd {a} {b} rp = record
  { %a = div'-one
  ; %b = div'-one
  ; f = f
  }
  where
  f : (x : Nat) -> x div' a -> x div' b -> x div' 1
  f x xa xb = transport (cong (x div'_) (rp x xa xb)) div'-refl

relatively-prime->gcdⁱ : {a b : Int} -> RelativelyPrime a b -> GCD a b (int 1)
relatively-prime->gcdⁱ {a} {b} rp = record
  { %a = div-one
  ; %b = div-one
  ; non-neg = inj-l tt
  ; f = f
  }
  where
  f : (x : Int) -> x div a -> x div b -> x div (int 1)
  f (nonneg x) x%a x%b = (int 1) , *-left-one >=> rp (nonneg x) (NonNeg-nonneg x) x%a x%b
  f (neg x)    x%a x%b =
    - (int 1) , minus-extract-left >=> cong -_ *-left-one >=>
                rp (pos x) (inj-l tt) (div-negate-left x%a) (div-negate-left x%b)


gcd->relatively-prime : {a b : Nat} -> GCD' a b 1 -> RP a b
gcd->relatively-prime g d da db = div'-antisym (GCD'.f g d da db) div'-one

gcdⁱ->relatively-prime : {a b : Int} -> GCD a b (int 1) -> RelativelyPrime a b
gcdⁱ->relatively-prime g d nonneg-d da db = div-one->one nonneg-d (GCD.f g d da db)


euclids-lemma/rp : {a b c : Nat} -> a div' (b *' c) -> RP a b -> a div' c
euclids-lemma/rp a%bc rp = euclids-lemma' a%bc (relatively-prime->gcd rp)


prime-divides-a-factor : (p : Prime') -> {a b : Nat}
                         -> ⟨ p ⟩ div' (a *' b) -> (⟨ p ⟩ div' a) ⊎ (⟨ p ⟩ div' b)
prime-divides-a-factor p@(p' , _) {a} {b} p-div with (decide-div p' a)
... | yes p%a = inj-l p%a
... | no ¬p%a = inj-r (euclids-lemma/rp p-div (prime->relatively-prime p ¬p%a))

relatively-prime-*' : {a b c : Nat} -> RP a b -> RP a c -> RP a (b *' c)
relatively-prime-*'     {b = zero}                 g _ = g
relatively-prime-*' {a} {b = b@(suc _)} {c = zero} _ g =
  transport (\i -> RP a (*'-commute {b} {zero} (~ i))) g
relatively-prime-*' {a@(suc _)} {b = b@(suc _)} {c = c@(suc _)} f-b f-c =
  no-shared-primes a (b *' c) f
  where
  ¬prime-div-one : (p : Prime') -> ¬(⟨ p ⟩ div' 1)
  ¬prime-div-one (_ , p) p%1 with ≤->≤i (div'->≤ p%1)
  ...                           | zero-≤i = 0-is-¬prime p
  ...                           | (suc-≤i zero-≤i) = 1-is-¬prime p

  f : (p : Prime') -> ⟨ p ⟩ div' a -> ⟨ p ⟩ div' (b *' c) -> Bot
  f p@(p' , _) p%a p%bc with (prime-divides-a-factor p {b} {c} p%bc)
  ... | inj-l p%b = Prime'.!=1 p (f-b p' p%a p%b)
  ... | inj-r p%c = Prime'.!=1 p (f-c p' p%a p%c)
relatively-prime-*' {zero} b@{suc _} c@{suc _} rp-b rp-c
  with (rp-zero rp-b) | (rp-zero rp-c)
...  | b==1            | c==1            = transport (\ i -> RP 0 (path i)) rp-b
  where
  path : b == b *' c
  path = b==1 >=> (\i -> (sym b==1 i) *' (sym c==1 i))

relatively-prime-^' : {a b : Nat} -> RP a b -> (k : Nat) -> RP a (b ^' k)
relatively-prime-^' {a} {b} g zero    = rp-one
relatively-prime-^'     {b} g (suc k) =
  relatively-prime-*' g (relatively-prime-^' g k)
