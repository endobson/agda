{-# OPTIONS --cubical --safe --exact-split #-}

module prime-gcd where

open import base
open import div
open import equality
open import gcd
open import nat
open import prime
open import prime-factorization
open import relation


prime-gcd' : (a b : Nat) -> {Pos' a} -> {Pos' b}
             -> ((p : Prime') -> ⟨ p ⟩ div' a -> ⟨ p ⟩ div' b -> Bot)
             -> GCD' a b 1
prime-gcd' a@(suc _) b@(suc _) pf = (gcd' a b 1 div'-one div'-one f)
  where
  f : (x : Nat) -> x div' a -> x div' b -> x div' 1
  f zero x%a x%b = zero-suc-absurd (sym (div'-zero->zero x%a))
  f (suc zero) _ _ = div'-one
  f x@(suc (suc _)) x%a x%b with (exists-prime-divisor {x} (suc-≤ (suc-≤ zero-≤)))
  ... | p , (prime-p , p%x) =
    bot-elim (pf (p , prime-p) (div'-trans p%x x%a) (div'-trans p%x x%b))

prime->relatively-prime : {a : Nat} -> (p : Prime') -> ¬ (⟨ p ⟩ div' a) -> GCD' ⟨ p ⟩ a 1
prime->relatively-prime {a} p ¬p%a =
  (gcd' ⟨ p ⟩ a 1 div'-one div'-one f)
  where
  f : (x : Nat) -> x div' ⟨ p ⟩ -> x div' a -> x div' 1
  f x x%p x%a with (prime-only-divisors p x%p)
  ... | inj-l pr = bot-elim (¬p%a (transport (\ i -> (pr i) div' a) x%a))
  ... | inj-r pr = (transport (\i -> (pr (~ i)) div' 1) div'-one)

distinct-primes->relatively-prime : {p1 p2 : Prime'} -> p1 != p2 -> GCD' ⟨ p1 ⟩ ⟨ p2 ⟩ 1
distinct-primes->relatively-prime {p1} {p2} path =
  prime->relatively-prime p1 (distinct-primes->¬div path)

prime-divides-a-factor : (p : Prime') -> {a b : Nat}
                         -> ⟨ p ⟩ div' (a *' b) -> (⟨ p ⟩ div' a) ⊎ (⟨ p ⟩ div' b)
prime-divides-a-factor p@(pv , _) {a} {b} p-div with (decide-div pv a)
... | yes p%a = inj-l p%a
... | no ¬p%a = inj-r (euclids-lemma' p-div (prime->relatively-prime p ¬p%a))

relatively-prime-*' : {a b c : Nat} -> GCD' a b 1 -> GCD' a c 1 -> GCD' a (b *' c) 1
relatively-prime-*' g@(gcd' a zero _ _ _ _) (gcd' a _ _ _ _ _) = g
relatively-prime-*' (gcd' a b@(suc _) _ _ _ _) g@(gcd' a zero _ _ _ _) =
  transport (\i -> GCD' a (*'-commute {b} {zero} (~ i)) 1) g
relatively-prime-*' (gcd' a@(suc _) b@(suc _) _ _ _ f-b) (gcd' a@(suc _) c@(suc _) _ _ _ f-c) =
  prime-gcd' a (b *' c) f
  where
  ¬prime-div-one : (p : Prime') -> ¬(⟨ p ⟩ div' 1)
  ¬prime-div-one (_ , p) p%1 with ≤->≤i (div'->≤ p%1)
  ...                           | zero-≤i = 0-is-¬prime p
  ...                           | (suc-≤i zero-≤i) = 1-is-¬prime p

  f : (p : Prime') -> ⟨ p ⟩ div' a -> ⟨ p ⟩ div' (b *' c) -> Bot
  f p@(p' , _) p%a p%bc with (prime-divides-a-factor p {b} {c} p%bc)
  ... | inj-l p%b = ¬prime-div-one p (f-b p' p%a p%b)
  ... | inj-r p%c = ¬prime-div-one p (f-c p' p%a p%c)
relatively-prime-*' {zero} b@{suc _} c@{suc _} gb gc
  with (gcd'-zero->id gb) | (gcd'-zero->id gc)
... | b==1 | c==1 = transport (\ i -> GCD' 0 (path i) 1) gb
  where
  path : b == b *' c
  path = b==1 >=> (\i -> (sym b==1 i) *' (sym c==1 i))

relatively-prime-^' : {a b : Nat} -> GCD' a b 1 -> (k : Nat) -> GCD' a (b ^' k) 1
relatively-prime-^' {a} {b} g zero    = gcd'-one
relatively-prime-^'     {b} g (suc k) =
  relatively-prime-*' g (relatively-prime-^' g k)
