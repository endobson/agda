{-# OPTIONS --cubical --safe --exact-split #-}

module prime-gcd where

open import abs
open import base
open import div
open import equality
open import gcd
open import int
open import nat
open import prime
open import prime-factorization
open import relation

RelativelyPrime' : Nat -> Nat -> Type₀
RelativelyPrime' a b = (d : Nat) -> d div' a -> d div' b -> d == 1

private
  RP = RelativelyPrime'

relatively-prime->gcd : {a b : Nat} -> RelativelyPrime' a b -> GCD' a b 1
relatively-prime->gcd {a} {b} rp = (gcd' div'-one div'-one f)
  where
  f : (x : Nat) -> x div' a -> x div' b -> x div' 1
  f x xa xb = transport (cong (x div'_) (rp x xa xb)) div'-refl

gcd->relatively-prime : {a b : Nat} -> GCD' a b 1 -> RelativelyPrime' a b
gcd->relatively-prime g d da db = div'-antisym (GCD'.f g d da db) div'-one

no-shared-primes : (a b : Nat)
                   -> ((p : Prime') -> ⟨ p ⟩ div' a -> ⟨ p ⟩ div' b -> Bot)
                   -> RP a b
no-shared-primes a b pf = f
  where
  f : (x : Nat) -> x div' a -> x div' b -> x == 1
  f zero x%a x%b = bot-elim (pf p p%a p%b)
    where
    a-zero : a == 0
    a-zero = div'-zero->zero x%a
    b-zero : b == 0
    b-zero = div'-zero->zero x%b

    p : Prime'
    p = 2 , 2-is-prime

    p%a : ⟨ p ⟩ div' a
    p%a = transport (\i -> 2 div' (a-zero (~ i))) div'-zero
    p%b : ⟨ p ⟩ div' b
    p%b = transport (\i -> 2 div' (b-zero (~ i))) div'-zero

  f (suc zero) _ _ = refl
  f x@(suc (suc _)) x%a x%b with (exists-prime-divisor {x} (suc-≤ (suc-≤ zero-≤)))
  ... | p , p%x =
    bot-elim (pf p (div'-trans p%x x%a) (div'-trans p%x x%b))


rp-one : {a : Nat} -> RP a 1
rp-one x xa x1 = div'-antisym x1 div'-one

rp-sym : {a b : Nat} -> RP a b -> RP b a
rp-sym rp x xa xb = rp x xb xa

prime->relatively-prime : {a : Nat} -> (p : Prime') -> ¬ (⟨ p ⟩ div' a) -> RP ⟨ p ⟩ a
prime->relatively-prime {a} p ¬p%a = f
  where
  f : (x : Nat) -> x div' ⟨ p ⟩ -> x div' a -> x == 1
  f x x%p x%a with (prime-only-divisors p x%p)
  ... | inj-l pr = bot-elim (¬p%a (transport (\ i -> (pr i) div' a) x%a))
  ... | inj-r pr = pr

distinct-primes->relatively-prime : {p1 p2 : Prime'} -> p1 != p2 -> RP ⟨ p1 ⟩ ⟨ p2 ⟩
distinct-primes->relatively-prime {p1} {p2} path =
  prime->relatively-prime p1 (distinct-primes->¬div path)

euclids-lemma' : {a b c : Nat} -> a div' (b *' c) -> RP a b -> a div' c
euclids-lemma' {a} {b} {c} a%bc rp = result
  where
  int-a%bc : (int a) div (int b * int c)
  int-a%bc = transport (\i -> (int a) div ((int-inject-*' {b} {c} i))) (div'->div a%bc)
  result : a div' c
  result = (div->div' (euclids-lemma int-a%bc (gcd'->gcd/nat (relatively-prime->gcd rp))))

prime-divides-a-factor : (p : Prime') -> {a b : Nat}
                         -> ⟨ p ⟩ div' (a *' b) -> (⟨ p ⟩ div' a) ⊎ (⟨ p ⟩ div' b)
prime-divides-a-factor p@(p' , _) {a} {b} p-div with (decide-div p' a)
... | yes p%a = inj-l p%a
... | no ¬p%a = inj-r (euclids-lemma' p-div (prime->relatively-prime p ¬p%a))

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
  with (gcd'-zero->id (relatively-prime->gcd rp-b))
     | (gcd'-zero->id (relatively-prime->gcd rp-c))
... | b==1 | c==1 = transport (\ i -> RP 0 (path i)) rp-b
  where
  path : b == b *' c
  path = b==1 >=> (\i -> (sym b==1 i) *' (sym c==1 i))

relatively-prime-^' : {a b : Nat} -> RP a b -> (k : Nat) -> RP a (b ^' k)
relatively-prime-^' {a} {b} g zero    = rp-one
relatively-prime-^'     {b} g (suc k) =
  relatively-prime-*' g (relatively-prime-^' g k)
