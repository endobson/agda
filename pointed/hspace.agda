{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.hspace where

open import base
open import cubical
open import connected
open import equality-path
open import equivalence.base
open import funext
open import hlevel.base
open import isomorphism
open import pointed.base
open import pointed.pushout
open import pointed.suspension
open import pushout
open import pushout.identites
open import suspension.flattening
open import truncation.generic
open import truncation.generic.path
open import univalence
open import equivalence

module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  record HSpaceStr : Type ℓ where
    constructor hspace-str
    field
      μ : A -> A -> A
      μ-left-★ : ∀ a -> μ ★A a == a
      μ-right-★ : ∀ a -> μ a ★A == a
      μ-★ : μ-left-★ ★A == μ-right-★ ★A

HSpace : (ℓ : Level) -> Type (ℓ-suc ℓ)
HSpace ℓ = Σ[ A∙ ∈ Type∙ ℓ ] (HSpaceStr A∙)

ConnectedHSpace : (ℓ : Level) -> Type (ℓ-suc ℓ)
ConnectedHSpace ℓ = Σ[ ((A , _) , _) ∈ HSpace ℓ ] (isConnected A)

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

private
  module _ {ℓ : Level} {A∙@(A , ★A) : Type∙ ℓ} where
    commute-HSpaceStr : HSpaceStr A∙ -> HSpaceStr A∙
    commute-HSpaceStr hStr =
      hspace-str (\x y -> μ y x) μ-right-★ μ-left-★ (sym μ-★)
      where
      open HSpaceStr hStr

  module _ {ℓ : Level}
    (((A∙ , hStr) , cH) : ConnectedHSpace ℓ) where
    open HSpaceStr hStr

    isEquiv-μ₂ : ∀ a -> isEquiv (\x -> μ a x)
    isEquiv-μ₂ = isEquiv-μ₁ ((A∙ , commute-HSpaceStr hStr) , cH)

module _ {ℓ : Level}
  (H@((A∙@(A , ★A) , hStr) , cH) : ConnectedHSpace ℓ) where
  open HSpaceStr hStr

  hopf-fibration : Susp A -> Type ℓ
  hopf-fibration = Susp-rec (\a -> ua (μ a , isEquiv-μ₂ H a))

  -- hopf-fibration∙ : Susp A -> Type∙ ℓ
  -- hopf-fibration∙ a' = hopf-fibration a' , elim a'
  --   where
  --   elim : (a' : Susp A) -> hopf-fibration a'
  --   elim north = ★A
  --   elim south = ★A
  --   elim (meridian a i) = outS ans'
  --     where
  --     eq : A ≃ A
  --     eq = (μ a , isEquiv-μ₂ H a)

  --     ans : ua (μ a , isEquiv-μ₂ H a) i
  --     ans = ua-glue₀ eq i ★A

  --     ans'₁ : Sub (ua eq i) (i ∨ ~ i)
  --                 (\{ (i = i0) -> ★A
  --                   ; (i = i1) -> (μ a ★A)
  --                   })
  --     ans'₁ = inS ans


  --     ans' : Sub (ua eq i) (i ∨ ~ i)
  --                (\{ (i = i0) -> ★A
  --                  ; (i = i1) -> ★A
  --                  })
  --     ans' = ?

  private
    μ' : A × A -> A
    μ' (a₁ , a₂) = μ a₁ a₂

    μ⁻¹ : A -> A -> A
    μ⁻¹ x y = isEqInv (isEquiv-μ₁ H y) x

    μ-path₁ : ∀ x y -> μ⁻¹ (μ x y) y == x
    μ-path₁ x y = isEqRet (isEquiv-μ₁ H y) x
    μ-path₂ : ∀ x y -> (μ (μ⁻¹ x y) y) == x
    μ-path₂ x y = isEqSec (isEquiv-μ₁ H y) x

    step1 : Iso (Σ (Susp A) hopf-fibration) (Pushout proj₂ μ')
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

  hopf-join-eq∙ : (Σ∙ (Susp∙ A∙) hopf-fibration ★A) ≃∙ Join∙ A∙ A∙
  hopf-join-eq∙ = ef , fp
    where
    ef : Σ (Susp A) hopf-fibration ≃ Join A A
    ef = f-step₁ >eq> f-step₂ >eq> f-step₃ >eq> f-step₄
      where
      f-step₁ : (Σ (Susp A) hopf-fibration) ≃ (Pushout proj₂ μ')
      f-step₁ = isoToEquiv step1
      f-step₂ : (Pushout proj₂ μ') ≃ (Pushout μ' proj₂)
      f-step₂ = isoToEquiv step2
      f-step₃ : (Pushout μ' proj₂) ≃ (Pushout (\ (x , y) -> (μ (μ⁻¹ x y) y)) proj₂)
      f-step₃ = Pushout-center-eq μ' proj₂ step3
      f-step₄ : (Pushout (\ (x , y) -> (μ (μ⁻¹ x y) y)) proj₂) ≃ Join A A
      f-step₄ = isoToEquiv (Pushout-function-iso μ-inv (\_ -> refl))
        where
        μ-inv : ∀ ((x , y) : A × A) -> (μ (μ⁻¹ x y) y) == x
        μ-inv (x , y) = isEqSec (isEquiv-μ₁ H y) x

    f : Σ (Susp A) hopf-fibration -> Join A A
    f = fst ef

    fp : f (north , ★A) == inj-l ★A
    fp = sym (pushout.glue (★A , ★A))

  hopf-construction :
    (Σ (Susp A) hopf-fibration) == Join A A
  hopf-construction = cong fst (Type∙-path hopf-join-eq∙)
