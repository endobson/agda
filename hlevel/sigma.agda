{-# OPTIONS --cubical --safe --exact-split #-}

-- h-level for Σ types

module hlevel.sigma where

open import base
open import cubical
open import equality-path
open import hlevel.base
open import relation
open import sigma

private
  variable
    ℓ : Level
    A A₁ A₂ : Type ℓ
    B : A -> Type ℓ

isContrΣ : isContr A -> ((x : A) -> isContr (B x)) -> isContr (Σ A B)
isContrΣ {A = A} {B = B} (a , p) q = elem , path-f
  where
  elem : Σ A B
  elem = (a , q a .fst)
  h : (a : A) (b : B a) -> (q a) .fst == b
  h a b = (q a) .snd b

  path-f : (s2 : (Σ A B)) -> elem == s2
  path-f s2 i = (p (s2 .fst) i) , path-b i
    where
    path-b : PathP (\k -> B (p (s2 .fst) k)) (q a .fst) (s2 .snd)
    path-b i = h (p (s2 .fst) i) (transp (\ j -> B (p (s2 .fst) (i ∨ ~ j))) i (s2 .snd)) i

-- ΣProp== is in hlevel.base because it is needed earlier in construction

section-ΣProp== : (pB : (x : A) → isProp (B x)) {u v : Σ A B} ->
                  (∀ x -> (ΣProp== pB {u} {v} (cong fst x)) == x)
section-ΣProp== {A = A} pB {u} {v} p j i =
  (p i .fst) , isProp->PathP (\ i -> isOfHLevelPath 1 (pB (fst (p i)))
                                       (ΣProp== pB {u} {v} (cong fst p) i .snd)
                                       (p i .snd))
                                       refl refl i j


isPropΣ : isProp A -> ((a : A) -> isProp (B a)) -> isProp (Σ A B)
isPropΣ pA pB (a1 , _) (a2 , _) = ΣProp== pB (pA a1 a2)

uniqueProp->isPropΣ : ((a1 a2 : A) -> (B a1) -> (B a2) -> a1 == a2) ->
                      (isPropValuedPred B) -> isProp (Σ A B)
uniqueProp->isPropΣ unique isPropB (a1 , b1) (a2 , b2) =
  ΣProp-path (isPropB _) (unique a1 a2 b1 b2)

isOfHLevelΣ : (n : Nat) -> isOfHLevel n A -> ((x : A) -> isOfHLevel n (B x)) -> isOfHLevel n (Σ A B)
isOfHLevelΣ 0 = isContrΣ
isOfHLevelΣ 1 = isPropΣ
isOfHLevelΣ {B = B} (suc (suc n)) hA hB x0 x1 =
  let hΣ : isOfHLevel (suc n) (x0 Σ==T x1)
      hΣ = isOfHLevelΣ (suc n) (hA (fst x0) (fst x1))
                       (\ p -> (hB (p i1)) (substᵉ B p (snd x0)) (snd x1))
  in transport (\i -> isOfHLevel (suc n) (pathSigma==sigmaPath x0 x1 (~ i))) hΣ

isSetΣ : isSet A -> ((a : A) -> isSet (B a)) -> isSet (Σ A B)
isSetΣ = isOfHLevelΣ 2

isProp× : isProp A₁ -> isProp A₂ -> isProp (A₁ × A₂)
isProp× pA₁ pA₂ = isPropΣ pA₁ (\_ -> pA₂)

isSet× : isSet A₁ -> isSet A₂ -> isSet (A₁ × A₂)
isSet× sA₁ sA₂ = isSetΣ sA₁ (\_ -> sA₂)
