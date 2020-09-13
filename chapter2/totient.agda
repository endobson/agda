{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.totient where

open import base
open import equality
open import gcd.computational
open import gcd.propositional hiding (gcd'-unique)
open import list
open import list.nat
open import nat
open import prime-gcd
open import relatively-prime
open import relation

private
  record Totient (n : Nat) (k : Nat) : Type₀ where
    field
      pos-k : Pos' k
      k≤n : k ≤ n
      rp : RelativelyPrime⁰ k n


  isBoundedTotient : {n : Nat} -> isBounded (Totient n)
  isBoundedTotient {n} = (suc n) , (\ t -> trans-≤-< (Totient.k≤n t) (suc-≤ (same-≤ n)))

  decide-rp : (k n : Nat) -> Dec (RelativelyPrime⁰ k n)
  decide-rp k n = handle (decide-nat (gcd' k n) 1)
    where
    handle : Dec ((gcd' k n) == 1) -> Dec (RelativelyPrime⁰ k n)
    handle (no ¬p) = no (\ rp -> ¬p (gcd'-unique (relatively-prime->gcd rp)))
    handle (yes p) = yes (gcd->relatively-prime (transport (cong (GCD' k n) p) (gcd'-proof k n)))


  decide-totient : (n k : Nat) -> Dec (Totient n k)
  decide-totient n zero      = no (\ t -> (Totient.pos-k t))
  decide-totient n k@(suc _) = handle (decide-nat≤ k n) (decide-rp k n)
    where
    handle : Dec (k ≤ n) -> Dec (RelativelyPrime⁰ k n) -> Dec (Totient n k)
    handle (no ¬k≤n) _        = no (\ t -> ¬k≤n (Totient.k≤n t))
    handle (yes k≤n) (no ¬rp) = no (\ t -> ¬rp (Totient.rp t))
    handle (yes k≤n) (yes rp) = yes (record { k≤n = k≤n ; rp = rp })

  totients-full : (n : Nat) -> Σ (List Nat) (CanonicalList≥ (Totient n))
  totients-full n = list-reify isBoundedTotient (\ k -> decide-totient n k)

  totients : (n : Nat) -> (List Nat)
  totients n = ⟨ totients-full n ⟩

  totients-canonical : (n : Nat) -> (CanonicalList≥ (Totient n) (totients n))
  totients-canonical n = snd (totients-full n)

φ⁰ : (n : Nat) -> Nat
φ⁰ n = length (totients n)

φ : (n : Nat⁺) -> Nat
φ (n , _) = (φ⁰ n)

private
  totient-n-zero : {n : Nat} -> ¬ (Totient n zero)
  totient-n-zero t = Totient.pos-k t

  totient-one-one : (Totient 1 1)
  totient-one-one = record
    { k≤n = (same-≤ 1)
    ; rp = rp-one
    }

  totients-one : List Nat
  totients-one = 1 :: []

  totients-one-canonical : CanonicalList≥ (Totient 1) totients-one
  totients-one-canonical = ((co , ca) , nd) , sorted
    where
    co : ContainsOnly (Totient 1) totients-one
    co (0 , p)     = transport (cong (Totient 1) (sym p)) totient-one-one
    co {x} (suc i , p) = bot-elim ([]-¬contains {x = x} (i , p))

    ca : ContainsAll (Totient 1) totients-one
    ca {a} t = (0 , handle t)
      where
      handle : {n : Nat} -> Totient 1 n -> n == 1
      handle {zero} t  = bot-elim (Totient.pos-k t)
      handle {suc n} t = ≤-antisym (Totient.k≤n t) (n , +'-commute {n} {1})

    nd : NoDuplicates totients-one
    nd = (\()) , lift tt
    sorted : Sorted _≥_ totients-one
    sorted = (\()) , lift tt

  φ-one : φ⁰ 1 == 1
  φ-one = cong length (canonical-list-== (totients-canonical 1) totients-one-canonical)
