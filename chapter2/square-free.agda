{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.square-free where

open import base
open import commutative-monoid
open import div
open import equality
open import functions
open import hlevel
open import isomorphism
open import nat
open import order
open import order.instances.nat
open import prime
open import prime-factorization
open import relation
open import relatively-prime
open import sigma.base
open import unique-prime-factorization
open import unordered-list

SquareFree : Nat⁺ -> Type₀
SquareFree (n , _) = (p : Prime') (pf : PrimeFactorization n)
                     -> count p (PrimeFactorization.primes pf) ≤ 1

SquareFree⁰ : Nat -> Type₀
SquareFree⁰ zero = Bot
SquareFree⁰ (suc n) = SquareFree ((suc n) , tt)

isPropSquareFree : {n : Nat⁺} -> isProp (SquareFree n)
isPropSquareFree = isPropΠ2 (\_ _ -> isProp≤)

decide-square-free : (n : Nat⁺) -> Dec (SquareFree n)
decide-square-free n⁺@(n@(suc _) , n-pos) = answer
  where
  pf : PrimeFactorization n
  pf = compute-prime-factorization n⁺

  no-dupes : Dec (NoDuplicates (PrimeFactorization.primes pf))
  no-dupes = (decide-no-duplicates (PrimeFactorization.primes pf))

  answer : Dec (SquareFree n⁺)
  answer with no-dupes
  ... | (yes f) = (yes g)
    where
    g : (p : Prime') (pf2 : PrimeFactorization n) -> count p (PrimeFactorization.primes pf2) ≤ 1
    g p pf2 = transport (\i -> count p (PrimeFactorization.primes (pf-path i)) ≤ 1) (f p)
      where
      pf-path : pf == pf2
      pf-path = isPropPrimeFactorization pf pf2
  ... | (no ¬f) = (no ¬g)
    where
    ¬g : ¬ ((p : Prime') (pf2 : PrimeFactorization n) -> count p (PrimeFactorization.primes pf2) ≤ 1)
    ¬g g = ¬f (\p -> g p pf)

prime-square-free : (p : Prime') -> SquareFree (Prime'.nat⁺ p)
prime-square-free p@(p' , _) p2@(p2' , _) pf = handle (decide-nat p2' p')
  where
  pf-path : pf == (prime-prime-factorization p)
  pf-path = isPropPrimeFactorization _ _

  handle : Dec (p2' == p') -> count p2 (PrimeFactorization.primes pf) ≤ 1
  handle (yes p'-path) = (0 , full-path)
    where
    p-path : p2 == p
    p-path = ΣProp-path isPropIsPrime' p'-path

    full-path : count p2 (PrimeFactorization.primes pf) == 1
    full-path =
      (\i -> count p2 (PrimeFactorization.primes (pf-path i)))
      >=> count-== [] p-path

  handle (no ¬path) = (1 , cong suc full-path)
    where
    ¬p-path : p2 != p
    ¬p-path = ¬path ∘ (cong fst)

    full-path : count p2 (PrimeFactorization.primes pf) == 0
    full-path =
      (\i -> count p2 (PrimeFactorization.primes (pf-path i)))
      >=> count-!= [] ¬p-path

prime-power-¬square-free : {n : Nat} (p : Prime') -> n ≥ 2 ->
                           ¬ (SquareFree (prime-power⁺ p n))
prime-power-¬square-free {zero}        p n≥2 sf = zero-≮ n≥2
prime-power-¬square-free {suc zero}    p n≥2 sf = zero-≮ (pred-≤ n≥2)
prime-power-¬square-free {suc (suc n)} p n≥2 sf =
  (same-≮ (trans-≤ p-count-≤ sf-≤))
  where
  primes-base : UList Prime'
  primes-base = (PrimeFactorization.primes (prime-power-prime-factorization p n))

  primes' : UList Prime'
  primes' = (p :: (p :: primes-base))

  sf-≤ : count p primes' ≤ 1
  sf-≤ = sf p (prime-power-prime-factorization p (suc (suc n)))

  p-count-≤ : 2 ≤ count p primes'
  p-count-≤ = count p primes-base ,
    (+'-commute {count p primes-base} {2})
    >=> cong suc (sym (count-== primes-base refl))
    >=> sym (count-== (p :: primes-base) refl)

relatively-prime-square-free : (a b : Nat⁺) -> RelativelyPrime⁺ a b
                               -> SquareFree a -> SquareFree b -> SquareFree (a *⁺ b)
relatively-prime-square-free a⁺@(a , _) b⁺@(b , _) rp sf-a sf-b p@(p' , _) pf-ab =
  handle (decide-div p' a)
  where
  pf-a = compute-prime-factorization a⁺
  pf-b = compute-prime-factorization b⁺

  primes = PrimeFactorization.primes pf-ab
  primes-a = PrimeFactorization.primes pf-a
  primes-b = PrimeFactorization.primes pf-b

  path-pf : pf-ab == (*'-prime-factorization pf-a pf-b)
  path-pf = isPropPrimeFactorization _ _

  handle : Dec (p' div' a) -> count p primes ≤ 1
  handle (yes p%a) = 0 , count-path
    where
    count-a' : 1 ≤ count p primes-a
    count-a' = contains->count>0 (Iso.fun (prime-div-prime-factorization-∈-iso p pf-a) p%a)

    count-a : count p primes-a == 1
    count-a = ≤-antisym (sf-a p pf-a) count-a'

    ¬p%b : ¬ (p' div' b)
    ¬p%b p%b = <->!= (Prime'.>1 p) (sym (rp p' p%a p%b))

    count-b : count p primes-b == 0
    count-b = ¬contains->count==0 primes-b
                (¬p%b ∘ (Iso.inv (prime-div-prime-factorization-∈-iso p pf-b)))


    count-path : count p primes == 1
    count-path =
      cong (count p ∘ PrimeFactorization.primes) path-pf
      >=> CommMonoidʰ.preserves-∙ (countʰ p) primes-a primes-b
      >=> (\i -> count-a i +' count-b i)

  handle (no ¬p%a) = (fst count-b , cong (fst count-b +'_) count-path >=> snd count-b)
    where
    count-a : count p primes-a == 0
    count-a = ¬contains->count==0 primes-a
                (¬p%a ∘ (Iso.inv (prime-div-prime-factorization-∈-iso p pf-a)))


    count-b : count p primes-b ≤ 1
    count-b = sf-b p pf-b

    count-path : count p primes == count p primes-b
    count-path =
      cong (count p ∘ PrimeFactorization.primes) path-pf
      >=> CommMonoidʰ.preserves-∙ (countʰ p) primes-a primes-b
      >=> (\i -> count-a i +' count p primes-b)


¬square-free-*-left : {a : Nat⁺} -> ¬(SquareFree a) -> (b : Nat⁺) -> ¬ (SquareFree (a *⁺ b))
¬square-free-*-left {a} ¬sf-a b@(b' , _) sf-ab = ¬sf-a sf-a
  where
  sf-a : SquareFree a
  sf-a p pf-a = count-a
    where
    pf-b : PrimeFactorization b'
    pf-b = compute-prime-factorization b

    primes-a = (PrimeFactorization.primes pf-a)
    primes-b = (PrimeFactorization.primes pf-b)

    count-ab : (count p primes-a +' count p primes-b) ≤ 1
    count-ab = transport
      (\i -> CommMonoidʰ.preserves-∙ (countʰ p) primes-a primes-b i ≤ 1)
      (sf-ab p (*'-prime-factorization pf-a pf-b) )

    count-a : count p primes-a ≤ 1
    count-a = transport
      (\i -> (+'-commute {count p primes-a} {0} i) ≤ 1)
      (trans-≤ (+-both-≤⁺ (same-≤ (count p primes-a)) zero-≤) count-ab)


¬square-free-*-right : (a : Nat⁺) {b : Nat⁺} -> ¬(SquareFree b) -> ¬ (SquareFree (a *⁺ b))
¬square-free-*-right a@(a' , _) {b} ¬sf-b sf-ab = ¬sf-b sf-b
  where
  sf-b : SquareFree b
  sf-b p pf-b = count-b
    where
    pf-a : PrimeFactorization a'
    pf-a = compute-prime-factorization a

    primes-a = (PrimeFactorization.primes pf-a)
    primes-b = (PrimeFactorization.primes pf-b)

    count-ab : (count p primes-a +' count p primes-b) ≤ 1
    count-ab = transport
      (\i -> CommMonoidʰ.preserves-∙ (countʰ p) primes-a primes-b i ≤ 1)
      (sf-ab p (*'-prime-factorization pf-a pf-b) )

    count-b : count p primes-b ≤ 1
    count-b = (trans-≤ (+-both-≤⁺ zero-≤ (same-≤ (count p primes-b))) count-ab)
