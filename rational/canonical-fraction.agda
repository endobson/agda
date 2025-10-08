{-# OPTIONS --cubical --safe --exact-split #-}

module rational.canonical-fraction where

open import base
open import equality-path
open import fraction.canonical
open import hlevel.base
open import hlevel.sigma
open import rational
open import set-quotient
open import sigma.base
open import truncation

opaque
  unfolding ℚ

  private
    ℚ->∃!ℚ' : (q : ℚ) -> ∃![ c ∈ ℚ' ] ((ℚ'->ℚ c == q) × isCanonicalℚ' c)
    ℚ->∃!ℚ' = SetQuotientElim.liftContr isContr-C
      where
      C : (q : ℚ) -> Type₀
      C q = Σ[ c ∈ ℚ' ] ((ℚ'->ℚ c == q) × isCanonicalℚ' c)

      isProp-C : (q : ℚ') -> isProp (C [ q ])
      isProp-C q (r₁ , p₁ , c₁) (r₂ , p₂ , c₂) =
        ΣProp-path (isProp× (isSetℚ _ _) isProp-isCanonicalℚ')
          (ℚ'-r~-unique-canonical r₁ r₂
            (SetQuotientElim.pathRec isProp-r~ isEquivRel-r~ r₁ r₂ [r₁]=[r₂])
            c₁ c₂)
        where
        [r₁]=[r₂] : Path ℚ [ r₁ ] [ r₂ ]
        [r₁]=[r₂] = p₁ >=> sym p₂

      isContr-C : (q : ℚ') -> isContr (C [ q ])
      isContr-C q =
        (fst Σr , eq/ _ q (proj₁ (snd Σr)) , proj₂ (snd Σr)) ,
        isProp-C q _
        where
        Σr : Σ[ r ∈ ℚ' ] (r r~ q × isCanonicalℚ' r)
        Σr = ℚ'->canonical q

  ℚ->ℚ' : ℚ -> ℚ'
  ℚ->ℚ' q = ∃!-val (ℚ->∃!ℚ' q)

  ℚ->ℚ'->ℚ : (q : ℚ) -> ℚ'->ℚ (ℚ->ℚ' q) == q
  ℚ->ℚ'->ℚ q = proj₁ (∃!-prop (ℚ->∃!ℚ' q))

  isCanonical-ℚ->ℚ' : (q : ℚ) -> isCanonicalℚ' (ℚ->ℚ' q)
  isCanonical-ℚ->ℚ' q = proj₂ (∃!-prop (ℚ->∃!ℚ' q))
