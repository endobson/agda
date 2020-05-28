{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel where

open import base
open import equality
open import relation

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C : Type ℓ

-- Deifined in core
-- isContr : Type ℓ -> Type ℓ
-- isContr A = Σ[ x ∈ A ] ((y : A) -> x == y)

isProp : Type ℓ -> Type ℓ
isProp A = ∀ (x y : A) -> x == y

isSet : Type ℓ -> Type ℓ
isSet A = ∀ (x y : A) -> isProp (x == y)


module _ {A : I -> Type ℓ} {x : A i0} {y : A i1} where
  toPathP : transp A i0 x == y -> PathP A x y
  toPathP p i = hcomp (\ j -> (\ { (i = i0) -> x
                                 ; (i = i1) -> p j}))
                      (transp (\ j -> A (i ∧ j)) (~ i) x)

isProp->PathP : {B : I -> Type ℓ} -> ((i : I) -> isProp (B i)) -> (b0 : (B i0)) (b1 : (B i1))
                -> PathP (\i -> B i) b0 b1
isProp->PathP hB b0 b1 = toPathP (hB _ _ _)

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




isOfHLevel : Nat -> Type ℓ -> Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = ∀ (x y : A) -> isOfHLevel (suc n) (x == y)


isOfHLevelDep : Nat -> {A : Type ℓ₁} -> (B : A -> Type ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
isOfHLevelDep 0 {A = A} B =  
  {a : A} -> Σ[ b ∈ B a ] ({a' : A} (b' : B a') (p : a == a') -> PathP (\i -> (B (p i))) b b')
isOfHLevelDep 1 {A = A} B =
  {a0 a1 : A} (b0 : B a0) (b1 : B a1) (p : a0 == a1) -> PathP (\i -> B (p i)) b0 b1
isOfHLevelDep (suc (suc n)) {A = A} B =
  {a0 a1 : A} (b0 : B a0) (b1 : B a1)
  -> isOfHLevelDep (suc n) {A = a0 == a1} (\p -> PathP (\i -> B (p i)) b0 b1)


isOfHLevel->isOfHLevelDep : (n : Nat) {A : Type ℓ₁} {B : A -> Type ℓ₂}
  -> (h : (a : A) -> isOfHLevel n (B a)) -> isOfHLevelDep n {A = A} B
isOfHLevel->isOfHLevelDep 0 h {a} = 
  (h a .fst , (\ b p -> isProp->PathP (\i -> isContr->isProp (h (p i))) (h a .fst) b))
isOfHLevel->isOfHLevelDep 1 h = (\ b0 b1 p -> isProp->PathP (\i -> (h (p i))) b0 b1)
isOfHLevel->isOfHLevelDep (suc (suc n)) {A = A} {B = B} h {a0} {a1} b0 b1 =
  isOfHLevel->isOfHLevelDep (suc n) (\ p -> helper a1 p b1)
  where
  helper : (a1 : A) (p : a0 == a1) (b1 : B a1) ->
    isOfHLevel (suc n) (PathP (\i -> (B (p i))) b0 b1)
  helper a1 p b1 = J (\ a1 p -> ∀ b1 -> isOfHLevel (suc n) (PathP (\i -> (B (p i))) b0 b1))
                     (\ _ -> h _ _ _) p b1
  
isOfHLevelΠ : {A : Type ℓ₁} {B : A -> Type ℓ₂} (n : Nat) -> ((x : A) -> (isOfHLevel n (B x)))
              -> isOfHLevel n ((x : A) -> B x)
isOfHLevelΠ {A = A} {B = B} 0 h = (\x -> fst (h x)) , (\ f i y -> (snd (h y)) (f y) i)
isOfHLevelΠ {A = A} {B = B} 1 h f g i a = h a (f a) (g a) i
isOfHLevelΠ {A = A} {B = B} (suc (suc n)) h f g =
   subst (isOfHLevel (suc n)) funExtPath (isOfHLevelΠ (suc n) (\a -> h a (f a) (g a)))


isSetΠ : {A : Type ℓ₁} {B : A -> Type ℓ₂} -> ((x : A) -> isSet (B x)) -> isSet ((x : A) -> (B x))
isSetΠ = isOfHLevelΠ 2


private
  Dec->Stable : Dec A -> Stable A
  Dec->Stable (yes a) ¬¬a = a
  Dec->Stable (no ¬a) ¬¬a = bot-elim (¬¬a ¬a)

  Bot-isProp : isProp Bot
  Bot-isProp x _ = bot-elim x

  isProp¬ : (A : Type ℓ) -> isProp (¬ A)
  isProp¬ _ ¬x ¬y i x = Bot-isProp (¬x x) (¬y x) i


  Stable==->isSet : ((x y : A) -> Stable (x == y)) -> isSet A
  Stable==->isSet {A = A} st a0 a1 p1 p2 j i =
    let
     -- Push through the stabilizer
     f : (x : A) -> a0 == x -> a0 == x
     f x p = st a0 x (\h -> h p)
     -- Pushing through the stabilizer is a constant function
     fIsConst : (x : A) -> (p q : a0 == x) -> f x p == f x q
     fIsConst x p q i = st a0 x (isProp¬ _ (\h -> h p) (\h -> h q) i)
     -- Shows that we can extend to any path starting from refl
     rem : (p : a0 == a1) -> PathP (\i -> a0 == p i) (f a0 refl) (f a1 p)
     rem p j = f (p j) (\ i -> p (i ∧ j))

    in hcomp (\ k -> (\ { (i = i0) -> f a0 refl k
                        ; (i = i1) -> fIsConst a1 p1 p2 j k
                        ; (j = i0) -> rem p1 i k
                        ; (j = i1) -> rem p2 i k})) a0
          

Discrete->isSet : Discrete A -> isSet A
Discrete->isSet d = Stable==->isSet (\ x y -> Dec->Stable (d x y))

