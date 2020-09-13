{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.mobius where

open import base
open import chapter2.square-free
open import chapter2.divisors
open import commutative-monoid
open import div
open import equality
open import functions
open import hlevel
open import int
open import list
open import list.discrete
open import nat
open import prime
open import prime-factorization
open import prime-power-factorization
open import prime-gcd
open import relation
open import relatively-prime
open import ring
open import ring.lists
open import ring.implementations
open import sigma
open import unique-prime-factorization

import unordered-list as ul

μ-inner : (n : Nat⁺) -> Dec (SquareFree n) -> Int
μ-inner n (yes _) =
  (neg zero) ^ (ul.length (PrimeFactorization.primes (compute-prime-factorization n)))
μ-inner _ (no _) = zero-int

μ : Nat⁺ -> Int
μ n = μ-inner n (decide-square-free n)

μ⁰ : Nat -> Int
μ⁰ zero    = zero-int
μ⁰ (suc n) = μ ((suc n) , tt)

square-free-μ : {n : Nat⁺} -> SquareFree n -> (pf : PrimeFactorization ⟨ n ⟩)
               -> μ n == (neg zero) ^ (ul.length (PrimeFactorization.primes pf))
square-free-μ {n⁺} sf pf with (decide-square-free n⁺)
... | (yes _) = (\i -> (neg zero) ^ (ul.length (PrimeFactorization.primes (pf-path i))))
  where
  pf-path : (compute-prime-factorization n⁺) == pf
  pf-path = isPropPrimeFactorization _ _
... | (no ¬sf) = bot-elim (¬sf sf)


¬square-free-μ : {n : Nat⁺} -> ¬(SquareFree n) -> μ n == zero-int
¬square-free-μ {n} ¬sf = handle (decide-square-free n)
  where
  handle : (s : Dec (SquareFree n)) -> μ-inner n s == zero-int
  handle (yes sf) = bot-elim (¬sf sf)
  handle (no _) = refl


μ1==1 : μ⁰ 1 == (int 1)
μ1==1 = refl

μp==-1 : (p : Prime') -> μ (Prime'.nat⁺ p) == (- (int 1))
μp==-1 p = square-free-μ (prime-square-free p) (prime-prime-factorization p)

μ⁰-path : (n : Nat⁺) -> μ⁰ ⟨ n ⟩ == μ n
μ⁰-path (suc n , tt) = refl


relatively-prime-μ : {a b : Nat⁺} -> RelativelyPrime⁺ a b
                     -> μ (a *⁺ b) == μ a * μ b
relatively-prime-μ {a} {b} rp = handle (decide-square-free a) (decide-square-free b)
  where
  handle : Dec (SquareFree a) -> Dec (SquareFree b) -> μ (a *⁺ b) == μ a * μ b
  handle _ (no ¬sf-b) =
    begin
      μ (a *⁺ b)
    ==< ¬square-free-μ (¬square-free-*-right a {b} ¬sf-b) >
      (int 0)
    ==< sym (*-right-zero {μ a}) >
      μ a * (int 0)
    ==< *-right {μ a} (sym (¬square-free-μ ¬sf-b)) >
      μ a * μ b
    end
  handle (yes sf-a) (yes sf-b) =
    begin
      μ (a *⁺ b)
    ==< square-free-μ sf-ab pf-ab >
      (- (int 1)) ^ (ul.length (primes-a ul.++ primes-b))
    ==< CommMonoidʰ.preserves-∙ (^ʰ (- (int 1)) ∘ʰ ul.lengthʰ) primes-a primes-b >
      (- (int 1)) ^ (ul.length primes-a) * (- (int 1)) ^ (ul.length primes-b)
    ==< *-left (sym (square-free-μ sf-a pf-a)) >
      μ a * (- (int 1)) ^ (ul.length primes-b)
    ==< *-right {μ a} (sym (square-free-μ sf-b pf-b)) >
      μ a * μ b
    end
    where
    pf-a = compute-prime-factorization a
    pf-b = compute-prime-factorization b
    pf-ab = *'-prime-factorization pf-a pf-b

    primes-a = PrimeFactorization.primes pf-a
    primes-b = PrimeFactorization.primes pf-b

    sf-ab : SquareFree (a *⁺ b)
    sf-ab = relatively-prime-square-free a b rp sf-a sf-b
  handle (no ¬sf-a) (yes sf-b) =
    begin
      μ (a *⁺ b)
    ==< ¬square-free-μ (¬square-free-*-left {a} ¬sf-a b) >
      (int 0)
    ==<>
      (int 0) * μ b
    ==< *-left (sym (¬square-free-μ ¬sf-a)) >
      μ a * μ b
    end


relatively-prime-μ⁰ : {a b : Nat} -> RelativelyPrime⁰ a b
                     -> μ⁰ (a *' b) == μ⁰ a * μ⁰ b
relatively-prime-μ⁰ {a = 0} rp = refl
relatively-prime-μ⁰ {a = a@(suc _)} {b = b@zero} rp =
  cong μ⁰ (*'-commute {a} {b}) >=> (*-commute {μ⁰ b} {μ⁰ a})
relatively-prime-μ⁰ {a = a@(suc _)} {b = b@(suc _)} rp =
  relatively-prime-μ {a = (a , tt)} {b = (b , tt)} rp


divisor-sum : (n : Nat⁺) -> (d : Nat -> Int) -> Int
divisor-sum n f = sum IntSemiring (map f (divisors n))

divisor-sum-μ : (n : Nat⁺) -> Int
divisor-sum-μ n = divisor-sum n μ⁰

divisor-sum-μ-rp : {a b : Nat⁺} -> RelativelyPrime⁺ a b
                   -> divisor-sum-μ (a *⁺ b) == divisor-sum-μ a * divisor-sum-μ b
divisor-sum-μ-rp {a} {b} rp =
  begin
    divisor-sum-μ (a *⁺ b)
  ==<>
    sum' (map μ⁰ (divisors (a *⁺ b)))
  ==< sym (sum-map-Permutation IntSemiring μ⁰ (*'-divisors-permutation a b rp)) >
    sum' (map μ⁰ (*'-divisors a b))
  ==<>
    sum' (map μ⁰ (map (\ (x , y) -> x *' y) cp))
  ==< cong sum' (double-map μ⁰ (\ (x , y) -> x *' y) cp) >
    sum' (map (\ (x , y) -> μ⁰ (x *' y)) cp)
  ==<>
    sum' (cartesian-product' (\ x y -> μ⁰ (x *' y)) da db)
  ==< cong sum' (sym (cartesian-product-ind'-path {f = (\ x y -> μ⁰ (x *' y))} {da} {db})) >
    sum' (cartesian-product-ind' (\ x y -> μ⁰ (x *' y)) da db)
  ==<>
    sum' (cartesian-product-ind da db (\ x y _ _ -> μ⁰ (x *' y)))
  ==< (\i -> sum' (cartesian-product-ind da db (\ x y cx cy -> f-path x y cx cy i))) >
    sum' (cartesian-product-ind da db (\ x y _ _ -> μ⁰ x * μ⁰ y))
  ==< cong sum' (cartesian-product-ind'-path {f = (\ x y -> μ⁰ x * μ⁰ y)} {da} {db}) >
    sum' (cartesian-product' (\ x y -> μ⁰ x * μ⁰ y) da db)
  ==<>
    sum' (map (\ (x , y) -> μ⁰ x * μ⁰ y) cp)
  ==< cong sum' (sym (double-map curry-* (×-map μ⁰ μ⁰) cp)) >
    sum' (map curry-* (map (×-map μ⁰ μ⁰) cp))
  ==< cong (\ x -> sum' (map curry-* x)) (cartesian-product-map μ⁰ μ⁰ (divisors a) (divisors b)) >
    sum' (cartesian-product' _*_ (map μ⁰ (divisors a)) (map μ⁰ (divisors b)))
  ==< sum-cartesian-product IntSemiring (map μ⁰ (divisors a)) (map μ⁰ (divisors b)) >
    (sum' (map μ⁰ (divisors a))) * (sum' (map μ⁰ (divisors b)))
  ==<>
    divisor-sum-μ a * divisor-sum-μ b
  end
  where
  sum' = sum IntSemiring
  curry-* = (\ (x , y) -> x * y)
  da = (divisors a)
  db = (divisors b)
  cp = (cartesian-product da db)

  f-path : (x : Nat) (y : Nat) -> (contains x da) -> (contains y db)
           ->  μ⁰ (x *' y) == μ⁰ x * μ⁰ y
  f-path x y cx cy = relatively-prime-μ⁰ (divisors-relatively-prime rp x%a y%b)
    where
    x%a : x div' ⟨ a ⟩
    x%a = divisors-contains-only a cx
    y%b : y div' ⟨ b ⟩
    y%b = divisors-contains-only b cy

divisor-sum-μ-prime : (p : Prime') -> divisor-sum-μ (Prime'.nat⁺ p) == (int 0)
divisor-sum-μ-prime p =
  begin
    divisor-sum-μ p⁺
  ==<>
    sum' (map μ⁰ (divisors p⁺))
  ==< (\i -> (sum' (map μ⁰ (prime-divisors-path p i)))) >
    μ⁰ p' + (μ⁰ 1 + μ⁰ 0)
  ==< +-left (μ⁰-path p⁺) >
    μ p⁺ + (μ⁰ 1 + μ⁰ 0)
  ==< (\i -> (μp==-1 p i) + ((μ1==1 i) + (int 0))) >
    (- (int 1)) + ((int 1) + (int 0))
  ==<>
    (int 0)
  end
  where
  sum' = sum IntSemiring
  p' = ⟨ p ⟩
  p⁺ = (Prime'.nat⁺ p)

divisor-sum-μ-prime-power : (p : Prime') (n : Nat) -> (n > 0)
                            -> divisor-sum-μ (prime-power⁺ p n) == (int 0)
divisor-sum-μ-prime-power p zero n>0 = bot-elim (zero-≮ n>0)
divisor-sum-μ-prime-power p (suc zero) n>0 =
  transport (\i -> divisor-sum-μ (path (~ i)) == (int 0)) (divisor-sum-μ-prime p)
  where
  path : (prime-power⁺ p 1) == (Prime'.nat⁺ p)
  path = ΣProp-path isPropPos' ^'-right-one
divisor-sum-μ-prime-power p (suc n@(suc n')) _ =
  begin
    (divisor-sum-μ (prime-power⁺ p (suc n)))
  ==<>
    (sum' (map μ⁰ (divisors (prime-power⁺ p (suc n)))))
  ==< cong (\ x -> (sum' (map μ⁰ x))) (prime-power-divisors-path p (suc n)) >
    (sum' (map μ⁰ (divisors-of-prime-power p (suc n))))
  ==<>
    (μ⁰ (prime-power p (suc n))) + (sum' (map μ⁰ (divisors-of-prime-power p n)))
  ==< +-left (μ⁰-path (prime-power⁺ p (suc n))) >
    (μ (prime-power⁺ p (suc n))) + (sum' (map μ⁰ (divisors-of-prime-power p n)))
  ==< +-left (¬square-free-μ (prime-power-¬square-free p sn≥2)) >
    (sum' (map μ⁰ (divisors-of-prime-power p n)))
  ==< cong (\ x -> (sum' (map μ⁰ x))) (sym (prime-power-divisors-path p n)) >
    (divisor-sum-μ (prime-power⁺ p n))
  ==< (divisor-sum-μ-prime-power p n n>0) >
    (int 0)
  end
  where
  sum' = sum IntSemiring
  n>0 : n > 0
  n>0 = n' , +'-commute {n'} {1}
  sn≥2 : suc n ≥ 2
  sn≥2 = suc-≤ n>0

divisor-sum-μ-one : divisor-sum-μ 1⁺ == (int 1)
divisor-sum-μ-one =
  begin
    divisor-sum-μ 1⁺
  ==<>
    sum' (map μ⁰ (divisors 1⁺))
  ==< cong (sum' ∘ map μ⁰) one-divisors-path  >
    sum' (map μ⁰ (1 :: []))
  ==<>
    (μ⁰ 1) + (int 0)
  ==< +-right-zero >
    (μ⁰ 1)
  ==< μ1==1 >
    int 1
  end
  where
  sum' = sum IntSemiring

divisor-sum-μ->1 : {n : Nat⁺} -> ⟨ n ⟩ > 1 -> divisor-sum-μ n == (int 0)
divisor-sum-μ->1 {n} n>1 = handle {n} (compute-ppf n>1)
  where
  handle : {n : Nat⁺} -> (PrimePowerFactorization ⟨ n ⟩) -> divisor-sum-μ n == (int 0)
  handle (ppf-base p n@(suc n' , _)) = divisor-sum-μ-prime-power p (suc n') (suc-≤ zero-≤)
  handle (ppf-combine {a'} {b'} ppf-a ppf-b rp) =
    begin
      divisor-sum-μ (a *⁺ b)
    ==< divisor-sum-μ-rp {a = a} {b} rp >
      divisor-sum-μ a * divisor-sum-μ b
    ==< *-left (handle {a} ppf-a) >
      (int 0)
    end
    where
    a : Nat⁺
    a = a' , ppf->pos ppf-a
    b : Nat⁺
    b = b' , ppf->pos ppf-b
