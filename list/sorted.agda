{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module list.sorted {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} (_≤_ : Rel A ℓ₂)  where

open import equality
open import functions
open import list hiding (insert)

Sorted : Pred (List A) (ℓ-max ℓ₁ ℓ₂)
Sorted [] = Lift (ℓ-max ℓ₁ ℓ₂) Top
Sorted (a :: as) = ContainsOnly (a ≤_) as × Sorted as

sorted-[] : Sorted []
sorted-[] = lift tt

sorted-singleton : (a : A) -> Sorted [ a ]
sorted-singleton a = ≤all , sorted-[]
  where
  ≤all : {a2 : A} -> contains a2 [] -> a ≤ a2
  ≤all c = bot-elim ([]-¬contains c)

module algo (trans≤ : Transitive _≤_) (connex≤ : Connex _≤_) where

  private
    sorted-cons : (a1 a2 : A) -> (as : List A) -> (a1 ≤ a2) -> (Sorted (a2 :: as))
                  -> Sorted (a1 :: a2 :: as)
    sorted-cons a1 a2 as lt (co-a2 , s-as) = co-a1 , co-a2 , s-as
      where
      co-a1 : ContainsOnly (a1 ≤_) (a2 :: as)
      co-a1 {b} ([]      , r , path) = transport (\i -> a1 ≤ (::-injective' path (~ i))) lt
      co-a1 {b} (_ :: l , r , path) = trans≤ lt (co-a2 (l , r , ::-injective path))

  insert : (a : A) -> List A -> List A
  insert a [] = [ a ]
  insert a (a2 :: as) = handle (connex≤ a a2)
    where
    handle : (a ≤ a2 ⊎ a2 ≤ a) -> List A
    handle (inj-l a≤a2) = a :: a2 :: as
    handle (inj-r a2≤a) = a2 :: (insert a as)

  insert-permutation : (a : A) -> (as : List A) -> Permutation A (insert a as) (a :: as)
  insert-permutation a [] = permutation-same [ a ]
  insert-permutation a (a2 :: as) with (connex≤ a a2)
  ... | (inj-l a≤a2) = permutation-same (a :: a2 :: as)
  ... | (inj-r a2≤a) =
    permutation-compose
      (permutation-cons a2 (insert-permutation a as))
      (permutation-swap a2 a as)


  insert-sorted : (a : A) -> {as : List A} -> (Sorted as) -> (Sorted (insert a as))
  insert-sorted a {[]}       _    = sorted-singleton a
  insert-sorted a {a2 :: as} (co-a2-as , s-as) with (connex≤ a a2)
  ... | (inj-l a≤a2) = sorted-cons a a2 as a≤a2 (co-a2-as , s-as)
  ... | (inj-r a2≤a) = (co-a2 , (insert-sorted a s-as))
    where
    co-a2' : ContainsOnly (a2 ≤_) (a :: as)
    co-a2' ([]     , r , path) = transport (\i -> a2 ≤ (::-injective' path (~ i))) a2≤a
    co-a2' (_ :: l , r , path) = co-a2-as (l , r , ::-injective path)

    co-a2 : ContainsOnly (a2 ≤_) (insert a as)
    co-a2 = co-a2' ∘ (permutation-contains (insert-permutation a as))

  sort : List A -> List A
  sort []        = []
  sort (a :: as) = (insert a (sort as))

  sort-permutation : (as : List A) -> (Permutation A (sort as) as)
  sort-permutation [] = permutation-empty
  sort-permutation (a :: as) =
    permutation-compose
      (insert-permutation a (sort as))
      (permutation-cons a (sort-permutation as))

  sort-sorted : (as : List A) -> (Sorted (sort as))
  sort-sorted [] = sorted-[]
  sort-sorted (a :: as) = (insert-sorted a (sort-sorted as))
