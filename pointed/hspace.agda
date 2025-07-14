{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.hspace where

open import base
open import connected
open import equality-path
open import equivalence.base
open import funext
open import hlevel.base
open import isomorphism
open import pointed.base
open import pointed.suspension
open import pushout
open import pushout.flattening
open import pushout.identites
open import suspension.flattening
open import truncation.generic
open import truncation.generic.path
open import univalence

module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  record HSpaceStr : Type ℓ where
    constructor hspace-str
    field
      μ : A -> A -> A
      μ-left-★ : ∀ a -> μ ★A a == a
      μ-right-★ : ∀ a -> μ a ★A == a
      μ-★ : μ-left-★ ★A == μ-right-★ ★A

module _ {ℓ : Level} {A∙@(A , ★A) : Type∙ ℓ} where
  commute-HSpaceStr : HSpaceStr A∙ -> HSpaceStr A∙
  commute-HSpaceStr hStr = 
    hspace-str (\x y -> μ y x) μ-right-★ μ-left-★ (sym μ-★)
    where
    open HSpaceStr hStr

HSpace : (ℓ : Level) -> Type (ℓ-suc ℓ)
HSpace ℓ = Σ[ A∙ ∈ Type∙ ℓ ] (HSpaceStr A∙)

ConnectedHSpace : (ℓ : Level) -> Type (ℓ-suc ℓ)
ConnectedHSpace ℓ = Σ[ ((A , _) , _) ∈ HSpace ℓ ] (isConnectedₙ 2 A)

module _ {ℓ : Level} {A : Type ℓ} where
  recenter-isContr : isContr A -> A -> isContr A
  recenter-isContr (_ , p) a = a , \x -> sym (p a) >=> p x


module _ {ℓ : Level} 
  ((((A , ★A) , hStr) , cH) : ConnectedHSpace ℓ) where
  open HSpaceStr hStr
  private
    isEquiv-μ₁★ : isEquiv (\x -> μ x ★A)
    isEquiv-μ₁★ = 
      subst isEquiv (sym (funExt μ-right-★)) (idIsEquiv A)

  isEquiv-μ₁ : ∀ a -> isEquiv (\x -> μ x a)
  isEquiv-μ₁ a = 
    ∥ₙ-elim (\_ -> h) handle-p p2
    where
    h : isProp (isEquiv (\x -> μ x a))
    h = isProp-isEquiv

    p1 : squashₙ 2 ★A == squashₙ 2 a
    p1 = isContr->isProp cH _ _
    p2 : Squashₙ 1 (★A == a)
    p2 = eqInv (squashed-path-eq 1 ★A a) p1

    handle-p : (p : ★A == a) -> isEquiv (\x -> μ x a)
    handle-p p = transport (\i -> isEquiv (\x -> μ x (p i))) isEquiv-μ₁★


module _ {ℓ : Level} 
  (((A∙ , hStr) , cH) : ConnectedHSpace ℓ) where
  open HSpaceStr hStr

  isEquiv-μ₂ : ∀ a -> isEquiv (\x -> μ a x)
  isEquiv-μ₂ = isEquiv-μ₁ ((A∙ , commute-HSpaceStr hStr) , cH)

module _ {ℓ : Level} 
  (H@(((A , ★A) , hStr) , cH) : ConnectedHSpace ℓ) where
  open HSpaceStr hStr

  hopf-construction₁ : Susp A -> Type ℓ
  hopf-construction₁ = Susp-rec (\a -> ua (μ a , isEquiv-μ₂ H a))
 
  private
    μ' : A × A -> A
    μ' (a₁ , a₂) = μ a₁ a₂

    μ⁻¹ : A -> A -> A
    μ⁻¹ x y = isEqInv (isEquiv-μ₁ H y) x

    μ-path₁ : ∀ x y -> μ⁻¹ (μ x y) y == x
    μ-path₁ x y = isEqRet (isEquiv-μ₁ H y) x
    μ-path₂ : ∀ x y -> (μ (μ⁻¹ x y) y) == x
    μ-path₂ x y = isEqSec (isEquiv-μ₁ H y) x

    step1 : Iso (Σ (Susp A) hopf-construction₁) (Pushout proj₂ μ')
    step1 = ΣSusp-iso (\a -> (μ a , isEquiv-μ₂ H a))

    step2 : Iso (Pushout proj₂ μ') (Pushout μ' proj₂)
    step2 = Pushout-swap-iso proj₂ μ'

    step3 : (A × A) ≃ (A × A)
    step3 = isoToEquiv (iso fwd bkw fb bf)
      where
      fwd : (A × A) -> (A × A)
      fwd (x , y) = (μ x y , y)
      bkw : (A × A) -> (A × A)
      bkw (x , y) = (μ⁻¹ x y , y)

      fb : ∀ x -> fwd (bkw x) == x
      fb (x , y) i = μ-path₂ x y i , y
      bf : ∀ x -> bkw (fwd x) == x
      bf (x , y) i = μ-path₁ x y i , y

    A²-path : (A × A) == (A × A)
    A²-path = ua step3

    proj₂-path : PathP (\i -> A²-path i -> A) proj₂ proj₂
    proj₂-path i a² = proj₂ (ua-unglue step3 i a²)

    proj₁-path : PathP (\i -> A²-path i -> A) μ' proj₁
    proj₁-path i a² = proj₁ (ua-unglue step3 i a²)

    step4 : (Pushout μ' proj₂) == (Join A A)
    step4 i = Pushout (proj₁-path i) (proj₂-path i)

  hopf-construction₂ : 
    (Σ (Susp A) hopf-construction₁) == Join A A
  hopf-construction₂ = 
    isoToPath (step1 >iso> step2) >=> step4
    















