{-# OPTIONS --cubical --safe --exact-split #-}

module relatively-prime where

open import base
open import cubical
open import div
open import equality
open import equivalence
open import hlevel
open import int
open import isomorphism
open import nat
open import prime
open import prime-factorization
open import relation

RelativelyPrime⁰ : Nat -> Nat -> Type₀
RelativelyPrime⁰ a b = (d : Nat) -> d div' a -> d div' b -> d == 1

RelativelyPrime⁺ : Nat⁺ -> Nat⁺ -> Type₀
RelativelyPrime⁺ a b = RelativelyPrime⁰ ⟨ a ⟩ ⟨ b ⟩

RelativelyPrime : Int -> Int -> Type₀
RelativelyPrime a b = (d : Int) -> NonNeg d -> d div a -> d div b -> d == (int 1)

private
  RP = RelativelyPrime⁰

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


rp-zero : {a : Nat} -> RP 0 a -> a == 1
rp-zero {a} rp = rp a div'-zero div'-refl

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

divisors-relatively-prime : {d1 d2 a b : Nat} -> RP a b -> d1 div' a -> d2 div' b -> RP d1 d2
divisors-relatively-prime rp d1%a d2%b p p%d1 p%d2 = rp p (div'-trans p%d1 d1%a) (div'-trans p%d2 d2%b)


relatively-primeⁱ->relatively-prime :
  {a b : Nat} -> (RelativelyPrime (int a) (int b)) -> RelativelyPrime⁰ a b
relatively-primeⁱ->relatively-prime rp d d%a d%b =
  nonneg-injective (rp (int d) tt (div'->div d%a) (div'->div d%b))

relatively-prime->relatively-primeⁱ :
  {a b : Nat} -> RelativelyPrime⁰ a b -> (RelativelyPrime (int a) (int b))
relatively-prime->relatively-primeⁱ rp (nonneg d) _ d%a d%b =
  cong int (rp d (div->div' d%a) (div->div' d%b))

isProp-RelativelyPrime⁰ : {a b : Nat} -> isProp (RelativelyPrime⁰ a b)
isProp-RelativelyPrime⁰ = isPropΠ3 (\_ _ _ -> isSetNat _ _)

isProp-RelativelyPrime : {a b : Int} -> isProp (RelativelyPrime a b)
isProp-RelativelyPrime = isPropΠ4 (\_ _ _ _ -> isSetInt _ _)

RelativelyPrime-RelativelyPrime-eq :
  {a b : Nat} -> (RelativelyPrime⁰ a b ≃ RelativelyPrime (int a) (int b))
RelativelyPrime-RelativelyPrime-eq =
  isoToEquiv (iso relatively-prime->relatively-primeⁱ
                  relatively-primeⁱ->relatively-prime
                  (\_ -> isProp-RelativelyPrime _ _)
                  (\_ -> isProp-RelativelyPrime⁰ _ _))
