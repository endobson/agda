{-# OPTIONS --cubical --safe --exact-split #-}

module sigma where

open import base
open import cubical
open import equality-path
open import equivalence
open import haequiv
open import hlevel.base
open import isomorphism
open import functions
open import relation

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ
    B : A -> Type ℓ

-- Alternative paths for Σ-types

_Σ==T_ : (a b : Σ A B) -> Type _
_Σ==T_ {B = B} a b = Σ ((a .fst) == (b .fst)) (\p -> transport (\i -> B (p i)) (snd a) == snd b)

private
  pathSigma-π1 : {a b : Σ A B} -> a == b -> a .fst == b .fst
  pathSigma-π1 p i = p i .fst

  filler-π2 : {a b : Σ A B} -> (p : a == b) -> I -> (i : I) -> (B (fst (p i)))
  filler-π2 {B = B} {a = a} p i =
    fill (\j -> (B (fst (p j))))
         (\j -> \ { (i = i0) -> transport-filler (\k -> B (fst (p k))) (snd a) j
                  ; (i = i1) -> snd (p j) })
         (inS (snd a))

  pathSigma-π2 : {a b : Σ A B} -> (p : a == b) -> substᵉ B (pathSigma-π1 p) (a .snd) == b .snd
  pathSigma-π2 p i = filler-π2 p i i1

pathSigma->sigmaPath : (a b : Σ A B) -> a == b -> a Σ==T b
pathSigma->sigmaPath _ _ p = (pathSigma-π1 p , pathSigma-π2 p)

private
  filler-comp : (a b : Σ A B) -> a Σ==T b -> I -> I -> Σ A B
  filler-comp {B = B} a b (p , q) i =
    hfill (\ j -> \ { (i = i0) -> a
                    ; (i = i1) -> (p i1 , q j) })
          (inS (p i , transport-filler (\j -> B (p j)) (snd a) i))

sigmaPath->pathSigma : (a b : Σ A B) -> a Σ==T b -> a == b
sigmaPath->pathSigma a b x i = filler-comp a b x i i1

private
  homotopy-π1 :(a b : Σ A B) (x : a Σ==T b)
    -> pathSigma-π1 (sigmaPath->pathSigma a b x) == fst x
  homotopy-π1 a b x i j = fst (filler-comp a b x j (~ i))

  homotopy-π2 : (a b : Σ A B) (x : a Σ==T b) (i : I)
    -> transport (\ j -> B (fst (filler-comp a b x j i))) (snd a) == snd b
  homotopy-π2 {B = B} a b x i j =
    comp (\ k -> B (fst (filler-comp a b x k (i ∨ j))))
         (\ k -> \ { (j = i0) -> transport-filler (\ k -> (B (fst (filler-comp a b x k i))))
                                                  (snd a) k
                   ; (j = i1) -> snd (sigmaPath->pathSigma a b x k)
                   ; (i = i0) -> snd (filler-comp a b x k j)
                   ; (i = i1) -> filler-π2 (sigmaPath->pathSigma a b x) j k})
         (snd a)

sigmaPath->pathSigma->sigmaPath : {a b : Σ A B} (x : a Σ==T b)
  -> pathSigma->sigmaPath _ _ (sigmaPath->pathSigma a b x) == x
sigmaPath->pathSigma->sigmaPath {a = a} p i =
  (homotopy-π1 a _ p i , homotopy-π2 a _ p (~ i))

pathSigma->sigmaPath->pathSigma : {a b : Σ A B} (p : a == b)
    -> sigmaPath->pathSigma a b (pathSigma->sigmaPath _ _ p) == p
pathSigma->sigmaPath->pathSigma {B = B} {a = a} {b = b} p i j =
  hcomp (\ k -> \ { (i = i1) -> (fst (p j) , filler-π2 p k j)
                  ; (i = i0) -> filler-comp a b (pathSigma->sigmaPath _ _ p) j k
                  ; (j = i0) -> (fst a , snd a)
                  ; (j = i1) -> (fst b , filler-π2 p k i1) })
        (fst (p j) , transport-filler (\ k -> B (fst (p k))) (snd a) j)

pathSigma==sigmaPath : (a b : Σ A B) -> (a == b) == (a Σ==T b)
pathSigma==sigmaPath a b =
  isoToPath (iso (pathSigma->sigmaPath a b)
                 (sigmaPath->pathSigma a b)
                 (sigmaPath->pathSigma->sigmaPath {a = a})
                 pathSigma->sigmaPath->pathSigma)

ΣProp-pathᵉ : ∀ {x y : Σ A B}
              -> ({a : A} -> isProp (B a))
              -> (x .fst) == (y .fst)
              -> x == y
ΣProp-pathᵉ h p i .fst = p i
ΣProp-pathᵉ {x = x} {y = y} h p i .snd = isProp->PathP (\i -> h {(p i)}) (x .snd) (y .snd) i

abstract
  ΣProp-path : ∀ {x y : Σ A B}
               -> ({a : A} -> isProp (B a))
               -> (x .fst) == (y .fst)
               -> x == y
  ΣProp-path = ΣProp-pathᵉ

×-map : {ℓA ℓB ℓC ℓD : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD}
        -> (A -> C) -> (B -> D) -> (A × B) -> (C × D)
×-map f g (a , b) = (f a , g b)


¬exists->forall : ¬ (Σ[ a ∈ A ] (B a)) -> (a : A) -> ¬ (B a)
¬exists->forall ne a b = ne (a , b)

-- Equivalences and isomorphisms

module _ where
  open Iso
  ×-iso : {ℓa ℓb ℓc ℓd : Level} -> {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} {D : Type ℓd} ->
          Iso A C -> Iso B D -> Iso (A × B) (C × D)
  (×-iso f g) .fun = ×-map (f .fun) (g .fun)
  (×-iso f g) .inv = ×-map (f .inv) (g .inv)
  (×-iso f g) .rightInv (c , d) = cong2 _,_ (f .rightInv c) (g .rightInv d)
  (×-iso f g) .leftInv  (a , b) = cong2 _,_ (f .leftInv a) (g .leftInv b)

×-equiv : {ℓa ℓb ℓc ℓd : Level} -> {A : Type ℓa} {B : Type ℓb} {C : Type ℓc} {D : Type ℓd} ->
          A ≃ C -> B ≃ D -> (A × B) ≃ (C × D)
×-equiv f g = isoToEquiv (×-iso (equivToIso f) (equivToIso g))

reindexΣ-iso : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
               (eq : B ≃ A) (C : A -> Type ℓ₃) -> Iso (Σ A C) (Σ B (\b -> (C (eqFun eq b))))
reindexΣ-iso {A = A} {B} eq C = i
  where
  open Iso
  i : Iso (Σ A C) (Σ B (\b -> (C (eqFun eq b))))
  i .fun (a , c) = (eqInv eq a , substᵉ C (sym (eqSec eq a)) c)
  i .inv (b , c) = (eqFun eq b , c)
  i .rightInv (b , c) = (\i -> path1 i , path2 i)
    where
    path1 : (eqInv eq (eqFun eq b)) == b
    path1 = eqRet eq b
    path-path' : (cong (eqFun eq) (eqRet eq b)) == (eqSec eq (eqFun eq b))
    path-path' = isHAEquiv.comm (equiv->isHAEquiv eq) b
    path2 : PathP (\k -> C (eqFun eq (path1 k))) (substᵉ C (sym (eqSec eq (eqFun eq b))) c) c
    path2 = symP (subst-filler2 C (cong (eqFun eq) (sym path1)) (sym (eqSec eq (eqFun eq b)))
                                  (cong sym path-path') c)
  i .leftInv (a , c) = (\i -> path1 i , path2 i)
    where
    path1 : (eqFun eq (eqInv eq a)) == a
    path1 = eqSec eq a
    path2 : PathP (\k -> C (path1 k)) (substᵉ C (sym (eqSec eq a)) c) c
    path2 = symP (subst-filler C (sym path1) c)

reindexΣ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
           (eq : B ≃ A) (C : A -> Type ℓ₃) -> (Σ A C) ≃ (Σ B (\b -> (C (eqFun eq b))))
reindexΣ {A = A} {B} eq C = isoToEquiv (reindexΣ-iso eq C)

existential-eq : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : A -> Type ℓ₂} {C : A -> Type ℓ₃} ->
                 ((a : A) -> B a ≃ C a) -> Σ A B ≃ Σ A C
existential-eq {A = A} {B} {C} f = isoToEquiv i
  where
  open Iso
  i : Iso (Σ A B) (Σ A C)
  i .fun (a , b) = (a , eqFun (f a) b)
  i .inv (a , c) = (a , eqInv (f a) c)
  i .rightInv (a , c) i = (a , eqSec (f a) c i)
  i .leftInv (a , b) i = (a , eqRet (f a) b i)

existential-iso : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : A -> Type ℓ₂} {C : A -> Type ℓ₃} ->
                 ((a : A) -> Iso (B a) (C a)) -> Iso (Σ A B) (Σ A C)
existential-iso {A = A} {B} {C} f = i
  where
  open Iso
  i : Iso (Σ A B) (Σ A C)
  i .fun (a , b) = (a , (f a) .fun b)
  i .inv (a , c) = (a , (f a) .inv c)
  i .rightInv (a , c) i = (a , (f a) .rightInv c i)
  i .leftInv (a , b) i = (a , (f a) .leftInv b i)


Decidable-∩ : {P : Pred A ℓ₁} {Q : Pred A ℓ₁} -> Decidable P -> Decidable Q -> Decidable (P ∩ Q)
Decidable-∩ {P = P} {Q} decP decQ a = handle (decP a) (decQ a)
  where
  handle : Dec (P a) -> Dec (Q a) -> Dec ((P ∩ Q) a)
  handle (yes p) (yes q) = yes (p , q)
  handle (yes p) (no ¬q) = no (¬q ∘ snd)
  handle (no ¬p) _       = no (¬p ∘ fst)
