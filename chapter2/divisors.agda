{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.divisors where

open import base
open import div
open import equality
open import gcd
open import lcm
open import lcm.exists
open import list
open import list.nat
open import list.sorted
open import nat
open import prime
open import prime-gcd
open import relation
open import unique-prime-factorization


import unordered-list as ul

private
  variable
    ℓ : Level
    A : Type ℓ

isBoundedDiv' : (n : Nat⁺) -> isBounded (_div' ⟨ n ⟩)
isBoundedDiv' (n , pos-n) = (suc n) , (\p -> suc-≤ (div'->≤ p {pos-n}))

private
  divisors-full : (n : Nat⁺) -> Σ (List Nat) (CanonicalList≥ (_div' ⟨ n ⟩))
  divisors-full n = list-reify (isBoundedDiv' n) (\d -> decide-div d ⟨ n ⟩)

divisors : (n : Nat⁺) -> List Nat
divisors n = fst (divisors-full n)

divisors-canonical : (n : Nat⁺) -> (CanonicalList≥ (_div' ⟨ n ⟩) (divisors n))
divisors-canonical n = (snd (divisors-full n))

divisors-contains-only : (n : Nat⁺) -> (ContainsOnly (_div' ⟨ n ⟩) (divisors n))
divisors-contains-only n = fst (fst (fst (snd (divisors-full n))))

module _ where
  divisors-of-one : List Nat
  divisors-of-one = 1 :: []

  divisors-of-one-canonical : CanonicalList≥ (_div' 1) divisors-of-one
  divisors-of-one-canonical = ((c-o , c-a) , nd) , sorted
    where
    c-o : ContainsOnly (_div' 1) divisors-of-one
    c-o (0 , path) = transport (cong (_div' 1) (sym path)) div'-one
    c-a : ContainsAll (_div' 1) divisors-of-one
    c-a {d} (x , path) = (0 , (*'-only-one-right {x} {d} path))
    nd : NoDuplicates divisors-of-one
    nd = (\()) , lift tt
    sorted : Sorted _≥_ divisors-of-one
    sorted = (\()) , lift tt


  one-divisors-path : divisors 1⁺ == 1 :: []
  one-divisors-path = canonical-list-== (divisors-canonical 1⁺) divisors-of-one-canonical


module _ where
  private
    divisors-of-prime : (p : Prime') -> List Nat
    divisors-of-prime (p , _) = p :: 1 :: []

    divisors-of-prime-canonical :
      (p : Prime') -> CanonicalList≥ (_div' ⟨ p ⟩) (divisors-of-prime p)
    divisors-of-prime-canonical p@(p' , is-prime) = ((c-o , c-a) , nd) , sorted
      where
      c-o : ContainsOnly (_div' ⟨ p ⟩) (divisors-of-prime p)
      c-o (0 , path) = transport (cong (_div' p') (sym path)) div'-refl
      c-o (1 , path) = transport (cong (_div' p') (sym path)) div'-one
      c-a : ContainsAll (_div' ⟨ p ⟩) (divisors-of-prime p)
      c-a {d} dp = handle (prime-only-divisors p dp)
        where
        handle : (d == p' ⊎ d == 1) -> contains d (divisors-of-prime p)
        handle (inj-l path) = (0 , path)
        handle (inj-r path) = (1 , path)
      nd : NoDuplicates (divisors-of-prime p)
      nd = ((\{(0 , path) -> p!=1 path}) , (\()) , lift tt)
        where
        p!=1 : p' != 1
        p!=1 p==1 = <->!= (Prime'.>1 p) (sym p==1)
      sorted : Sorted _≥_ (divisors-of-prime p)
      sorted = ((\{(0 , path) -> p≥a path}) , (\()) , lift tt)
        where
        p≥a : {a : Nat} -> (a == 1) -> p' ≥ a
        p≥a a==1 = transport (\i -> p' ≥ (a==1 (~ i))) (weaken-< (Prime'.>1 p))

  prime-divisors-path : (p : Prime') -> divisors (Prime'.nat⁺ p) == (⟨ p ⟩ :: 1 :: [])
  prime-divisors-path p =
    canonical-list-== (divisors-canonical (Prime'.nat⁺ p)) (divisors-of-prime-canonical p)

-- Divisors of prime powers

module _ (p : Prime') where

  private
    p' = fst p
    is-prime = snd p
    p-pos = Prime'.pos p
    p⁺ = Prime'.nat⁺ p

    ¬p-divides->1 : (n : Nat) {d : Nat} -> d div' (prime-power p n)
                    -> ¬ (p' div' d) -> d == 1
    ¬p-divides->1 zero    {d} d%pn  _    = div'-one->one d%pn
    ¬p-divides->1 (suc n) {d} d%psn ¬d%p = ¬p-divides->1 n d%pn ¬d%p
      where
      d%pn : d div' (prime-power p n)
      d%pn = euclids-lemma' d%psn (rp-sym (prime->relatively-prime p ¬d%p))

    ¬p-divides->pn : (n x d : Nat) -> (x *' d == (prime-power p n))
                     -> ¬(p' div' x) -> d == (prime-power p n)
    ¬p-divides->pn n x d x-path ¬p%x =
      sym (*'-left-one {d}) >=> *'-left (sym x==1) >=> x-path
      where
      x==1 : x == 1
      x==1 = (¬p-divides->1 n (d , *'-commute {d} {x} >=> x-path) ¬p%x)


    p-divides->%pn : (n x d : Nat) -> (x *' d == (prime-power p (suc n)))
                     -> p' div' x -> d div' (prime-power p n)
    p-divides->%pn n x d x-path (z , z-path) =
      (z , *'-left-injective p⁺ path)
      where
      path : p' *' (z *' d) == (prime-power p (suc n))
      path = sym (*'-assoc {p'} {z} {d})
             >=> *'-left (*'-commute {p'} {z} >=> z-path)
             >=> x-path

    split-prime-power-divisor :
      {n : Nat} {d : Nat} -> d div' (prime-power p (suc n))
      -> (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
    split-prime-power-divisor {n} {d} (x , x-path) =
      handle (decide-div p' x)
      where
      handle : (Dec (p' div' x)) -> (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
      handle (yes p%x) = inj-r (p-divides->%pn n x d x-path p%x)
      handle (no ¬p%x) = inj-l (¬p-divides->pn (suc n) x d x-path ¬p%x)

  divisors-of-prime-power : Nat -> List Nat
  divisors-of-prime-power zero       = 1 :: []
  divisors-of-prime-power n@(suc n') = (p' ^' n) :: (divisors-of-prime-power n')

  private
    contains-only-divisors-of-prime-power : (n : Nat) ->
      ContainsOnly (_div' (p' ^' n)) (divisors-of-prime-power n)
    contains-only-divisors-of-prime-power zero    (0 , path) =
      (1 , *'-left-one >=> path)
    contains-only-divisors-of-prime-power (suc n) (0 , path) =
      (1 , *'-left-one >=> path)
    contains-only-divisors-of-prime-power (suc n) (suc i , path) =
      div'-mult (contains-only-divisors-of-prime-power n (i , path)) p'

    sorted>-divisors-of-prime-power : (n : Nat) -> Sorted _>_ (divisors-of-prime-power n)
    sorted>-divisors-of-prime-power zero = sorted-singleton _>_ 1
    sorted>-divisors-of-prime-power (suc n) =
      (>all , sorted>-divisors-of-prime-power n)
      where
      >all : ContainsOnly (_< (p' *' (p' ^' n))) (divisors-of-prime-power n)
      >all {x} c = trans-≤-< x-lt p-lt
        where
        x-div : x div' (p' ^' n)
        x-div = contains-only-divisors-of-prime-power n c
        x-lt : x ≤ (p' ^' n)
        x-lt = div'->≤ x-div {^'-Pos' (Prime'.pos p) n}
        p-lt : (p' ^' n) < (p' ^' (suc n))
        p-lt = ^-suc-< (Prime'.>1 p) n


  divisors-of-prime-power-canonical :
    (n : Nat) -> CanonicalList≥ (_div' (p' ^' n)) (divisors-of-prime-power n)
  divisors-of-prime-power-canonical zero = divisors-of-one-canonical
  divisors-of-prime-power-canonical (suc n) = ((c-o , c-a) , nd) , sorted
    where
    c-o = contains-only-divisors-of-prime-power (suc n)
    c-a : ContainsAll (_div' (p' *' (p' ^' n))) (divisors-of-prime-power (suc n))
    c-a {d} dp = handle (split-prime-power-divisor {n} {d} dp)
      where
      handle : (d == (⟨ p ⟩ *' (⟨ p ⟩ ^' n)) ⊎ d div' (⟨ p ⟩ ^' n))
               -> contains d (divisors-of-prime-power (suc n))
      handle (inj-l path) = (0 , path)
      handle (inj-r rec) =
        cons-contains (⟨ p ⟩ *' (⟨ p ⟩ ^' n))
                      (canonical-contains-all (divisors-of-prime-power-canonical n) rec)

    nd : NoDuplicates (divisors-of-prime-power (suc n))
    nd = sorted>->no-duplicates (sorted>-divisors-of-prime-power (suc n))
    sorted : Sorted _≥_ (divisors-of-prime-power (suc n))
    sorted = sorted>->sorted≥ (sorted>-divisors-of-prime-power (suc n))

-- Divisors of product
private
  lcm-divides-product : {d1 d2 a b m : Nat} -> d1 div' a -> d2 div' b -> LCM' d1 d2 m -> m div' (a *' b)
  lcm-divides-product {d1} {d2} {a} {b} {m} d1%a d2%b l =
    LCM'.f l (a *' b) (div'-mult' d1%a b) (div'-mult d2%b a)

  relatively-prime-lcm : {a b : Nat} -> RelativelyPrime' a b -> LCM' a b (a *' b)
  relatively-prime-lcm {a} {b} rp = transport (\ i -> LCM' a b (path (~ i))) l
    where
    m = lcm a b
    l = lcm-proof a b

    path : (a *' b) == m
    path = lcm-gcd-prod-path l (relatively-prime->gcd rp) >=> *'-right-one

  module _ (a b : Nat⁺) where
    private
      a' = ⟨ a ⟩
      b' = ⟨ b ⟩

    *'-divisors : List Nat
    *'-divisors = cartesian-product' _*'_ (divisors a) (divisors b)

    *'-divisors-co : ContainsOnly (_div' (a' *' b')) *'-divisors
    *'-divisors-co {x} c = transport (\i -> (x-path i) div' (a' *' b')) xab%ab
      where
      c-info : Σ[ p ∈ (Nat × Nat) ]
                 ((contains p (cartesian-product (divisors a) (divisors b)))
                  × (proj₁ p *' proj₂ p == x))
      c-info = map-contains' (\ (a , b) -> a *' b) (cartesian-product (divisors a) (divisors b)) c

      xa : Nat
      xa = proj₁ (fst c-info)
      xb : Nat
      xb = proj₂ (fst c-info)

      c-xs : (contains xa (divisors a)) × (contains xb (divisors b))
      c-xs = cartesian-product-contains' (divisors a) (divisors b) (fst (snd c-info))
      x-path : (xa *' xb == x)
      x-path = (snd (snd c-info))

      xa%a : xa div' a'
      xa%a = divisors-contains-only a (proj₁ c-xs)
      xb%b : xb div' b'
      xb%b = divisors-contains-only b (proj₂ c-xs)

      xab%ab : (xa *' xb) div' (a' *' b')
      xab%ab = div'-mult-both xa%a xb%b
