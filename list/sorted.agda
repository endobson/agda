{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module list.sorted {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} (_≤_ : Rel A ℓ₂)  where

open import equality
open import functions
open import list hiding (insert)
open import sum

Sorted : Pred (List A) (ℓ-max ℓ₁ ℓ₂)
Sorted [] = Lift (ℓ-max ℓ₁ ℓ₂) Top
Sorted (a :: as) = ContainsOnly (a ≤_) as × Sorted as

sorted-[] : Sorted []
sorted-[] = lift tt

sorted-singleton : (a : A) -> Sorted [ a ]
sorted-singleton a = (\()) , sorted-[]

module algo (trans≤ : Transitive _≤_) (connex≤ : Connex _≤_) where

  private
    sorted-cons : (a1 a2 : A) -> (as : List A) -> (a1 ≤ a2) -> (Sorted (a2 :: as))
                  -> Sorted (a1 :: a2 :: as)
    sorted-cons a1 a2 as lt (co-a2 , s-as) = co-a1 , co-a2 , s-as
      where
      co-a1 : ContainsOnly (a1 ≤_) (a2 :: as)
      co-a1 {b} (zero  , path) = transport (\i -> a1 ≤ ( path (~ i))) lt
      co-a1 {b} (suc n , path) = trans≤ lt (co-a2 (n , path))

  insert : (a : A) -> List A -> List A
  insert-⊎ : {a a2 : A} -> (a ≤ a2 ⊎ a2 ≤ a) -> List A -> List A
  insert a [] = [ a ]
  insert a (a2 :: as) = insert-⊎ (connex≤ a a2) as
  insert-⊎ {a} {a2} (inj-l a≤a2) as = a :: a2 :: as
  insert-⊎ {a} {a2} (inj-r a2≤a) as = a2 :: (insert a as)

  insert-⊎-left : {a a2 : A} {s : (a ≤ a2 ⊎ a2 ≤ a)}
                  -> Left s
                  -> (as : List A)
                  -> insert-⊎ s as == a :: a2 :: as
  insert-⊎-left {s = inj-l _} _ as = refl

  insert-⊎-right : {a a2 : A} {s : (a ≤ a2 ⊎ a2 ≤ a)}
                   -> Right s
                   -> (as : List A)
                   -> insert-⊎ s as == a2 :: (insert a as)
  insert-⊎-right {s = inj-r _} _ as = refl


  insert-connex-left : (a a2 : A) (as : List A) -> (Left (connex≤ a a2))
                       -> insert a (a2 :: as) == a :: a2 :: as
  insert-connex-left a1 a2 as l = insert-⊎-left l as

  insert-connex-right : (a a2 : A) (as : List A) -> (Right (connex≤ a a2))
                        -> insert a (a2 :: as) == a2 :: (insert a as)
  insert-connex-right a1 a2 as l = insert-⊎-right l as



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
    co-a2' (zero  , path) = transport (\i -> a2 ≤ (path (~ i))) a2≤a
    co-a2' (suc n , path) = co-a2-as (n , path)

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

  module order (antisym≤ : Antisymmetric _≤_) where
    _≤list_ : A -> List A -> Type (ℓ-max ℓ₁ ℓ₂)
    a ≤list as = ∀ {x} -> contains x as -> a ≤ x

    sorted-≤list-:: : {a1 a2 : A} {as : List A}
                      -> a1 ≤ a2
                      -> Sorted (a2 :: as)
                      -> a1 ≤list (a2 :: as)
    sorted-≤list-:: {a1 = a1} lt _       (0     , p) = transport (\i -> a1 ≤ (p (~ i))) lt
    sorted-≤list-::           lt (f , s) (suc n , p) = trans≤ lt (f (n , p))


    insert-list≤->== : {a : A} {as : List A} -> a ≤list as -> insert a as == a :: as
    insert-list≤->== {a} {[]} f = refl
    insert-list≤->== {a} {a2 :: as} f = handle (connex≤ a a2) refl
      where
      handle : (x : (a ≤ a2 ⊎ a2 ≤ a)) -> x == (connex≤ a a2)
               -> insert a (a2 :: as) == a :: a2 :: as
      handle (inj-l _) p = insert-connex-left a a2 as (transport (\i -> Left (p i)) tt)
      handle (inj-r a2≤a) p =
        insert-connex-right a a2 as (transport (\i -> Right (p i)) tt)
        >=> rec-path >=> flip-as
        where
        a==a2 : a == a2
        a==a2 = antisym≤ (f (0 , refl)) a2≤a

        f' : a ≤list as
        f' = f ∘ (cons-contains a2)

        rec-path : a2 :: (insert a as) == a2 :: a :: as
        rec-path = cong (a2 ::_) (insert-list≤->== f')

        flip-as : a2 :: a :: as == a :: a2 :: as
        flip-as i = (a==a2 (~ i)) :: (a==a2 i) :: as
