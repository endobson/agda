{-# OPTIONS --cubical --safe --exact-split #-}

module list.nat where

open import base
open import equality
open import fin
open import list
open import list.discrete
open import nat
open import relation

private
  variable
    ℓ : Level

allNatsUnder : Nat -> List Nat
allNatsUnder zero    = []
allNatsUnder (suc n) = n :: allNatsUnder n


allNatsUnder< : {n : Nat} -> ContainsAll (_< n) (allNatsUnder n)
allNatsUnder< {zero}          lt          = bot-elim (zero-≮ lt)
allNatsUnder< {suc n}         (zero  , p) = [] , allNatsUnder n , (\i -> pred (p i) :: allNatsUnder n)
allNatsUnder< {suc n} {a = a} (suc i , p) = handle (allNatsUnder< {n} (i , cong pred p))
  where
  handle : contains a (allNatsUnder n) -> contains a (allNatsUnder (suc n))
  handle (l , r , path) = (n :: l) , r , cong (n ::_) path

onlyNatsUnder< : {n : Nat} -> ContainsOnly (_< n) (allNatsUnder n)
onlyNatsUnder< {n} = transport (\i -> ContainsOnly (_< n) (path (same-≤ n) i))
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
all-nats-no-duplicates n a = handle (split-nat< a n)
  where
  all-nats-≥->count0 : {m : Nat} (n : Nat) -> (m ≥ n) -> count m (allNatsUnder n) == 0
  all-nats-≥->count0 zero    _  = refl
  all-nats-≥->count0 (suc n) gt =
    count-!= (allNatsUnder n) (\p -> (<->!= gt (sym p)))
    >=> (all-nats-≥->count0 n (pred-≤ (right-suc-≤ gt)))

  all-nats-<->count1 : (m n : Nat) -> (m < n) -> count m (allNatsUnder n) == 1
  all-nats-<->count1 m zero    lt = bot-elim (zero-≮ lt)
  all-nats-<->count1 m (suc n) (zero  , path) =
    count-== (allNatsUnder n) (cong pred path)
    >=> cong suc (all-nats-≥->count0 n (zero , (sym (cong pred path))))
  all-nats-<->count1 m (suc n) lt@(suc i , path) =
    count-!= (allNatsUnder n) (<->!= (i , cong pred path))
    >=> all-nats-<->count1 m n (i , cong pred path)

  handle : (a < n ⊎ n ≤ a) -> count a (allNatsUnder n) ≤ 1
  handle (inj-l a<n) = (0 , all-nats-<->count1 a n a<n)
  handle (inj-r n≤a) = (1 , cong suc (all-nats-≥->count0 n n≤a))

allBounded : {P : Pred Nat ℓ} -> (b : isBounded P) -> ContainsAll P (allNatsUnder ⟨ b ⟩)
allBounded {P} (_ , f) p = allNatsUnder< (f p)

private
  exactBoundedDecidable : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
                          -> ContainsExactlyOnce P (filter dec (allNatsUnder ⟨ b ⟩))
  exactBoundedDecidable b dec =
    (filter-contains-only dec (allNatsUnder ⟨ b ⟩) ,
     filter-contains-all dec (allBounded b)) ,
    filter-no-duplicates dec {as = allNatsUnder ⟨ b ⟩} (all-nats-no-duplicates ⟨ b ⟩)

list-reify : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
              -> Σ (List Nat) (ContainsExactlyOnce P)
list-reify b dec = l , proof
  where
  l = (filter dec (allNatsUnder ⟨ b ⟩))
  proof = exactBoundedDecidable b dec
