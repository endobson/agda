{-# OPTIONS --cubical --safe --exact-split #-}

module list.nat where

open import base
open import equality
open import fin
open import list
open import list.discrete
open import list.filter
open import list.sorted
open import list.unordered
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

all-nats-sorted : (n : Nat) -> Sorted _>_ (allNatsUnder n)
all-nats-sorted zero    = lift tt
all-nats-sorted (suc n) = (onlyNatsUnder< n , all-nats-sorted n)

allBounded : {P : Pred Nat ℓ} -> (b : isBounded P) -> ContainsAll P (allNatsUnder ⟨ b ⟩)
allBounded {P} (_ , f) p = allNatsUnder< _ (f p)

sorted>->sorted≥ : {as : List Nat} -> Sorted _>_ as -> Sorted _≥_ as
sorted>->sorted≥ {[]}      s = s
sorted>->sorted≥ {a :: as} (co , s) = (\ c -> pred-≤ (right-suc-≤ (co c))) , sorted>->sorted≥ s

CannonicalList≥ : (P : Pred Nat ℓ) -> List Nat -> Type ℓ
CannonicalList≥ P as = ContainsExactlyOnce P as × Sorted _≥_ as

cannonical-list-== : {P : Pred Nat ℓ} {as bs : List Nat}
                     -> CannonicalList≥ P as -> CannonicalList≥ P bs
                     -> as == bs
cannonical-list-== {P = P} {as} {bs} (ce1-a , sa) (ce1-b , sb) =
  begin
    as
  ==< sym (sorted-== sa) >
    sort as
  ==< sym (order-unorder-== as) >
    order (unorder as)
  ==< cong order (unorder-permutation (contains-exactly-once->permutation ce1-a ce1-b))  >
    order (unorder bs)
  ==< order-unorder-== bs >
    sort bs
  ==< sorted-== sb >
    bs
  end
  where
    dec≥ : Decidable2 _≥_
    dec≥ x y = decide-nat≤ y x
    ord≥ : TotalOrder _≥_
    ord≥ = total-order-≥

    open total _≥_ dec≥ ord≥


private
  exactBoundedDecidable : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
                          -> ContainsExactlyOnce P (filter dec (allNatsUnder ⟨ b ⟩))
  exactBoundedDecidable b dec =
    (filter-contains-only dec (allNatsUnder ⟨ b ⟩) ,
     filter-contains-all dec (allNatsUnder ⟨ b ⟩) (allBounded b)) ,
    filter-no-duplicates dec (allNatsUnder ⟨ b ⟩) (all-nats-no-duplicates ⟨ b ⟩)

  cannonicalBoundedDecidable :
    {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
    -> CannonicalList≥ P (filter dec (allNatsUnder ⟨ b ⟩))
  cannonicalBoundedDecidable b dec =
    (((filter-contains-only dec (allNatsUnder ⟨ b ⟩) ,
       filter-contains-all dec (allNatsUnder ⟨ b ⟩) (allBounded b)) ,
      filter-no-duplicates dec (allNatsUnder ⟨ b ⟩) (all-nats-no-duplicates ⟨ b ⟩)) ,
     (filter-sorted dec (sorted>->sorted≥ (all-nats-sorted ⟨ b ⟩))))

list-reify : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
              -> Σ (List Nat) (CannonicalList≥ P)
list-reify b dec = l , proof
  where
  l = (filter dec (allNatsUnder ⟨ b ⟩))
  proof = cannonicalBoundedDecidable b dec
