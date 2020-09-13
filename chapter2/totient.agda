{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.totient where

open import base
open import div
open import equality
open import functions
open import gcd.computational
open import gcd.propositional hiding (gcd'-unique)
open import list
open import list.nat
open import nat
open import prime
open import prime-gcd
open import relatively-prime
open import relation

private
  record Totient (n : Nat) (k : Nat) : Type₀ where
    field
      pos-k : Pos' k
      k≤n : k ≤ n
      rp : RelativelyPrime⁰ k n

    k<n : n > 1 -> k < n
    k<n n>1 = strengthen-≤ k≤n k!=n
      where
      k!=n : k != n
      k!=n k==n = <->!= n>1 (sym (rp n (transport (\i -> (k==n i) div' k) div'-refl) div'-refl))


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


module _ (p : Prime') where
  p' = ⟨ p ⟩
  private

    small-positives : (n : Nat) -> List Nat
    small-positives zero = []
    small-positives n@(suc n') = n :: small-positives n'

    small-positives-contains-only-≤ : (n : Nat) -> ContainsOnly (_≤ n) (small-positives n)
    small-positives-contains-only-≤ zero {x} c = bot-elim ([]-¬contains {x = x} c)
    small-positives-contains-only-≤ (suc n) (0     , path) = 0 , path
    small-positives-contains-only-≤ (suc n) (suc i , ai)   =
      right-suc-≤ (small-positives-contains-only-≤ n (i , ai))

    small-positives-contains-only-< : (n : Nat) -> ContainsOnly (_< n) (small-positives (pred n))
    small-positives-contains-only-< zero {x} c = bot-elim ([]-¬contains {x = x} c)
    small-positives-contains-only-< (suc n) c = suc-≤ (small-positives-contains-only-≤ n c)

    small-positives-contains-only-pos : (n : Nat) -> ContainsOnly Pos' (small-positives n)
    small-positives-contains-only-pos zero {x} c = bot-elim ([]-¬contains {x = x} c)
    small-positives-contains-only-pos (suc n) (0     , path) = transport (cong Pos' (sym path)) tt
    small-positives-contains-only-pos (suc n) (suc i , ai)   =
      small-positives-contains-only-pos n (i , ai)

    small-positives-contains-all : (n : Nat) -> ContainsAll (Pos' ∩ (_≤ n)) (small-positives n)
    small-positives-contains-all n {a = zero}  (() , _)
    small-positives-contains-all zero    {a = suc a} (_ , lt) = bot-elim (zero-≮ lt)
    small-positives-contains-all (suc n) {a = suc a} (_ , (0 , p))     = (0 , p)
    small-positives-contains-all (suc n) {a = suc a} (pos-a , (suc i , p)) =
      cons-contains (suc n) (small-positives-contains-all n {a = suc a} (pos-a , (i , cong pred p)))

    small-positives-sorted : (n : Nat) -> Sorted _>_ (small-positives n)
    small-positives-sorted 0       = lift tt
    small-positives-sorted (suc n) =
      (small-positives-contains-only-< (suc n) , small-positives-sorted n)

    small-positives-length : (n : Nat) -> length (small-positives n) == n
    small-positives-length 0 = refl
    small-positives-length (suc n) = cong suc (small-positives-length n)

    totient-prime : {k : Nat} -> Pos' k -> k < p' -> Totient p' k
    totient-prime {k} pos-k k<p = record
      { k≤n = weaken-< k<p
      ; pos-k = pos-k
      ; rp = rp
      }
      where
      ¬p%k : ¬(p' div' k)
      ¬p%k p%k = same-≮ (trans-<-≤ k<p (div'->≤ p%k {pos-k}))

      rp : RelativelyPrime⁰ k p'
      rp = rp-sym (prime->relatively-prime p ¬p%k)


    totients-prime : List Nat
    totients-prime = small-positives (pred p')

    totients-prime-canonical : CanonicalList≥ (Totient p') totients-prime
    totients-prime-canonical = ((co , ca) , nd) , sorted
      where

      co : ContainsOnly (Totient p') totients-prime
      co {k} c = totient-prime (small-positives-contains-only-pos (pred p') c)
                               (small-positives-contains-only-< p' c)

      ca : ContainsAll (Totient p') totients-prime
      ca t = small-positives-contains-all (pred p')
               (Totient.pos-k t , pred-≤ (Totient.k<n t (Prime'.>1 p)))

      nd : NoDuplicates totients-prime
      nd = sorted>->no-duplicates (small-positives-sorted (pred p'))
      sorted : Sorted _≥_ totients-prime
      sorted = sorted>->sorted≥ (small-positives-sorted (pred p'))

  φ-prime : φ⁰ p' == (pred p')
  φ-prime = cong length (canonical-list-== (totients-canonical p') totients-prime-canonical)
            >=> small-positives-length (pred p')
