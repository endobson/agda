{-# OPTIONS --cubical --safe --exact-split #-}

module list.nat where

open import base
open import equality
open import fin
open import list
open import list.discrete
open import list.filter
open import nat
open import relation

private
  variable
    ℓ : Level

allNatsUnder : Nat -> List Nat
allNatsUnder zero    = []
allNatsUnder (suc n) = n :: allNatsUnder n


allNatsUnder< : (n : Nat) -> ContainsAll (_< n) (allNatsUnder n)
allNatsUnder< zero    lt          = bot-elim (zero-≮ lt)
allNatsUnder< (suc n) (zero  , p) = zero , cong pred p
allNatsUnder< (suc n) (suc i , p) =
  cons-contains n (allNatsUnder< n (i , cong pred p))

onlyNatsUnder< : (n : Nat) -> ContainsOnly (_< n) (allNatsUnder n)
onlyNatsUnder< n = transport (\i -> ContainsOnly (_< n) (path (same-≤ n) i))
                             (filter-contains-only decide-P (allNatsUnder n))
  where

  decide-P : (a : Nat) -> Dec (a < n)
  decide-P a = decide-nat< a n

  path : {m : Nat} -> (m ≤ n) -> (filter decide-P (allNatsUnder m)) == (allNatsUnder m)
  path {zero} lt = refl
  path {suc m} lt = filter-keeps decide-P (allNatsUnder m) lt >=> cong (m ::_) helper
    where
    helper : (filter decide-P (allNatsUnder m)) == (allNatsUnder m)
    helper = path {m} (pred-≤ (right-suc-≤ lt))

all-nats-no-duplicates : (n : Nat) -> NoDuplicates (allNatsUnder n)
all-nats-no-duplicates zero = lift tt
all-nats-no-duplicates (suc n) = (¬c , all-nats-no-duplicates n)
  where
  ¬c : ¬ (contains n (allNatsUnder n))
  ¬c c = same-≮ (onlyNatsUnder< n c)

allBounded : {P : Pred Nat ℓ} -> (b : isBounded P) -> ContainsAll P (allNatsUnder ⟨ b ⟩)
allBounded {P} (_ , f) p = allNatsUnder< _ (f p)

private
  exactBoundedDecidable : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
                          -> ContainsExactlyOnce P (filter dec (allNatsUnder ⟨ b ⟩))
  exactBoundedDecidable b dec =
    (filter-contains-only dec (allNatsUnder ⟨ b ⟩) ,
     filter-contains-all dec (allNatsUnder ⟨ b ⟩) (allBounded b)) ,
    filter-no-duplicates dec (allNatsUnder ⟨ b ⟩) (all-nats-no-duplicates ⟨ b ⟩)

list-reify : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
              -> Σ (List Nat) (ContainsExactlyOnce P)
list-reify b dec = l , proof
  where
  l = (filter dec (allNatsUnder ⟨ b ⟩))
  proof = exactBoundedDecidable b dec
