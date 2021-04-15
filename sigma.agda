{-# OPTIONS --cubical --safe --exact-split #-}

module sigma where

open import base
open import cubical
open import equality
open import hlevel.base
open import isomorphism

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

  pathSigma-π2 : {a b : Σ A B} -> (p : a == b) -> subst B (pathSigma-π1 p) (a .snd) == b .snd
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
