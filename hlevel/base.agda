{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.base where

open import base
open import equality

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ
    B : A -> Type ℓ

-- Basic isOfHLevel

-- Deifined in core
-- isContr : Type ℓ -> Type ℓ
-- isContr A = Σ[ x ∈ A ] ((y : A) -> x == y)

isProp : Type ℓ -> Type ℓ
isProp A = (x y : A) -> x == y

isSet : Type ℓ -> Type ℓ
isSet A = (x y : A) -> isProp (x == y)

isOfHLevel : Nat -> Type ℓ -> Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = ∀ (x y : A) -> isOfHLevel (suc n) (x == y)

-- Increasing h-level

isContr->isProp : isContr A -> isProp A
isContr->isProp (x , p) a b i =
  hcomp (\j -> (\ { (i = i0) -> p a j
                  ; (i = i1) -> p b j})) x

isProp->isSet : isProp A -> isSet A
isProp->isSet h a0 a1 p1 p2 j i =
  hcomp (\k -> (\ { (i = i0) -> h a0 a0 k
                  ; (i = i1) -> h a0 a1 k
                  ; (j = i0) -> h a0 (p1 i) k
                  ; (j = i1) -> h a0 (p2 i) k })) a0

isOfHLevelSuc : (n : Nat) → isOfHLevel n A → isOfHLevel (suc n) A
isOfHLevelSuc 0 = isContr->isProp
isOfHLevelSuc 1 = isProp->isSet
isOfHLevelSuc (suc (suc n)) h a b = isOfHLevelSuc (suc n) (h a b)

-- Dependent h-level

module _ {A : I -> Type ℓ} {x : A i0} {y : A i1} where
  toPathP : transp A i0 x == y -> PathP A x y
  toPathP p i = hcomp (\ j -> (\ { (i = i0) -> x
                                 ; (i = i1) -> p j}))
                      (transp (\ j -> A (i ∧ j)) (~ i) x)

isProp->PathP : {B : I -> Type ℓ} -> ((i : I) -> isProp (B i)) -> (b0 : (B i0)) (b1 : (B i1))
                -> PathP (\i -> B i) b0 b1
isProp->PathP hB b0 b1 = toPathP (hB _ _ _)

isOfHLevelDep : Nat -> {A : Type ℓ₁} -> (B : A -> Type ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
isOfHLevelDep 0 {A = A} B =
  {a : A} -> Σ[ b ∈ B a ] ({a' : A} (b' : B a') (p : a == a') -> PathP (\i -> (B (p i))) b b')
isOfHLevelDep 1 {A = A} B =
  {a0 a1 : A} (b0 : B a0) (b1 : B a1) (p : a0 == a1) -> PathP (\i -> B (p i)) b0 b1
isOfHLevelDep (suc (suc n)) {A = A} B =
  {a0 a1 : A} (b0 : B a0) (b1 : B a1)
  -> isOfHLevelDep (suc n) {A = a0 == a1} (\p -> PathP (\i -> B (p i)) b0 b1)

isOfHLevel->isOfHLevelDep :
  (n : Nat) -> (h : (a : A) -> isOfHLevel n (B a)) -> isOfHLevelDep n {A = A} B
isOfHLevel->isOfHLevelDep 0 h {a} =
  (h a .fst , (\ b p -> isProp->PathP (\i -> isContr->isProp (h (p i))) (h a .fst) b))
isOfHLevel->isOfHLevelDep 1 h = (\ b0 b1 p -> isProp->PathP (\i -> (h (p i))) b0 b1)
isOfHLevel->isOfHLevelDep {A = A} {B = B} (suc (suc n)) h {a0} {a1} b0 b1 =
  isOfHLevel->isOfHLevelDep (suc n) (\ p -> helper a1 p b1)
  where
  helper : (a1 : A) (p : a0 == a1) (b1 : B a1) ->
    isOfHLevel (suc n) (PathP (\i -> (B (p i))) b0 b1)
  helper a1 p b1 = J (\ a1 p -> ∀ b1 -> isOfHLevel (suc n) (PathP (\i -> (B (p i))) b0 b1))
                     (\ _ -> h _ _ _) p b1
