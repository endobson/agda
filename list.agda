{-# OPTIONS --cubical --safe --exact-split #-}

module list where

open import base
open import relation
open import equality
open import monoid
open import nat

private
  variable
    ℓ : Level
    A B : Type ℓ


infixr 5 _::_
data List (A : Type ℓ) : Type ℓ where
  [] : List A
  _::_  : (a : A) -> List A -> List A

infixr 5 _++_
_++_ : List A -> List A -> List A
[] ++ l2 = l2
(a :: l1) ++ l2 = a :: (l1 ++ l2)

[_] : A -> List A
[ a ] = a :: []

map : (A -> B) -> List A -> List B
map f [] = []
map f (e :: l) = f e :: (map f l)

length : (l : List A) -> Nat
length []        = 0
length (_ :: as) = suc (length as)

NonEmpty : List A -> Set
NonEmpty [] = Bot
NonEmpty (_ :: _) = Top

data NonEmptyListBinaryRec (A : Type ℓ) : List A -> Type ℓ where
  elem  : (a : A) -> NonEmptyListBinaryRec A (a :: [])
  _:++:_ : ∀ {as bs} -> NonEmptyListBinaryRec A as -> NonEmptyListBinaryRec A bs
           -> NonEmptyListBinaryRec A (as ++ bs)

non-empty-list-binary-rec : (l : List A) -> {NonEmpty l} -> NonEmptyListBinaryRec A l
non-empty-list-binary-rec (e :: []) = elem e
non-empty-list-binary-rec (e :: l@(_ :: _)) = (elem e) :++: (non-empty-list-binary-rec l)

data ConcatTo {A : Type ℓ} : List A -> List A -> List A -> Set ℓ where
  concat-to-empty : ∀ as -> ConcatTo as [] as
  concat-to-cons : ∀ {as bs cs} a -> ConcatTo as bs cs -> ConcatTo (a :: as) (a :: bs) cs


map-inject-++ : (f : A -> B) {a1 a2 : List A} -> map f (a1 ++ a2) == (map f a1) ++ (map f a2)
map-inject-++ f {[]} = refl
map-inject-++ f {e :: a1} {a2} = cong (\x -> f e :: x) (map-inject-++ f {a1} {a2})


data Insertion (A : Type ℓ) : A -> (List A) -> (List A) -> Type ℓ where
  insertion-base : (a : A) -> (as : (List A)) -> Insertion A a as (a :: as)
  insertion-cons : {a : A} {as1 as2 : (List A)} -> (a2 : A)
                   -> (Insertion A a as1 as2) -> Insertion A a (a2 :: as1) (a2 :: as2)

data Permutation (A : Type ℓ) : (List A) -> (List A) -> Type ℓ where
  permutation-empty : Permutation A [] []
  permutation-cons  : {a : A} -> {as1 as2 as3 : List A}
                      -> Permutation A as1 as2
                      -> Insertion A a as2 as3
                      -> Permutation A (a :: as1) as3


insert : (A -> A -> Boolean) -> A -> List A -> List A
insert _ a [] = a :: []
insert _<_ a (a2 :: as) with a < a2
... | true = a :: (a2 :: as)
... | false = a2 :: (insert _<_ a as)

Insertion-insert : (_<_ : A -> A -> Boolean) -> (a : A) -> (as : (List A))
                   -> Insertion A a as (insert _<_ a as)
Insertion-insert _t a [] = insertion-base a []
Insertion-insert _<_ a (a2 :: as) with a < a2
... | true = insertion-base a (a2 :: as)
... | false = insertion-cons a2 (Insertion-insert _<_ a as)

insertion-sort : (A -> A -> Boolean) -> List A -> List A
insertion-sort _<_ [] = []
insertion-sort _<_ (a :: as) = (insert _<_ a (insertion-sort _<_ as))

Permutation-insertion-sort : (_<_ : A -> A -> Boolean) -> (as : List A)
                             -> Permutation A as (insertion-sort _<_ as)
Permutation-insertion-sort _<_ [] = permutation-empty
Permutation-insertion-sort _<_ (a :: as) =
  (permutation-cons (Permutation-insertion-sort _<_ as)
                    (Insertion-insert _<_ a (insertion-sort _<_ as)))

++-assoc : {a : List A} {b : List A} {c : List A} -> (a ++ b) ++ c == a ++ (b ++ c)
++-assoc {a = []} {b} {c} = refl
++-assoc {a = a :: as} {b} {c} = cong (a ::_) (++-assoc {a = as} {b} {c})

++-left-[] : {a : List A} -> ([] ++ a) == a
++-left-[] = refl

++-right-[] : {a : List A} -> (a ++ []) == a
++-right-[] {a = []} = refl
++-right-[] {a = a :: as} = cong (a ::_) (++-right-[] {a = as})


instance
  ListMonoid : Monoid (List A)
  ListMonoid {A} = record {
    ε = [];
    _∙_ = _++_;
    ∙-assoc = \ {m} {n} {o} -> ++-assoc {a = m} {n} {o};
    ∙-left-ε = ++-left-[];
    ∙-right-ε = ++-right-[]
    }


mapʰ : (f : A -> B) -> Monoidʰ (map f)
mapʰ f = record {
  preserves-ε = refl ;
  preserves-∙ = (\ x y -> map-inject-++ f {x} {y})
  }

concat : {{M : Monoid A}} -> List A -> A
concat {{M = M}} [] = Monoid.ε M
concat {{M = M}} (a :: l) = (Monoid._∙_ M) a (concat l)

concatʰ : {{M : Monoid A}} -> Monoidʰ (concat {{M}})
concatʰ {A = A} {{M = M}} = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  open Monoid M
  preserves-∙ : (x y : List A) -> concat (x ++ y) == (concat x) ∙ (concat y)
  preserves-∙ [] y = sym ∙-left-ε
  preserves-∙ (a :: l) y = cong (a ∙_) (preserves-∙ l y) >=> sym ∙-assoc

lengthʰ : Monoidʰ {D₁ = List A} length
lengthʰ = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  preserves-∙ : (xs ys : List A) -> length (xs ++ ys) == (length xs) +' (length ys)
  preserves-∙ [] ys = refl
  preserves-∙ (_ :: xs) ys = cong suc (preserves-∙ xs ys)

-- Injective
safe-tail : List A -> List A
safe-tail []        = []
safe-tail (_ :: as) = as

safe-head : A -> List A ->  A
safe-head x []        = x
safe-head x (a :: as) = a

::-injective : {a b : A} {as bs : List A} -> a :: as == b :: bs -> as == bs
::-injective p = cong safe-tail p

::-injective' : {a b : A} {as bs : List A} -> a :: as == b :: bs -> a == b
::-injective' {a = a} p = cong (safe-head a) p

++-injective-left : {as bs cs : List A} -> as ++ bs == as ++ cs -> bs == cs
++-injective-left {as = []}        p = p
++-injective-left {as = (a :: as)} p = (++-injective-left (::-injective p))
