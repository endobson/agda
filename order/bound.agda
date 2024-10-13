{-# OPTIONS --cubical --safe --exact-split #-}

module order.bound where

open import base
open import equality
open import hlevel
open import order
open import relation
open import sigma.base
open import truncation

private
  variable
    ℓI ℓD ℓ< ℓ≤ : Level
    I : Type ℓI

module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} {{PO : isPartialOrder D≤}} where
  isUpperBound : REL (I -> D) D _
  isUpperBound f d = ∀ i -> f i ≤ d
  isLowerBound : REL (I -> D) D _
  isLowerBound f d = ∀ i -> d ≤ f i

  isLeastUpperBound : REL (I -> D) D _
  isLeastUpperBound f d =
    isUpperBound f d ×
    ∀ ((d2 , _) : Σ D (isUpperBound f)) -> d ≤ d2
  isGreatestLowerBound : REL (I -> D) D _
  isGreatestLowerBound f d =
    isLowerBound f d ×
    ∀ ((d2 , _) : Σ D (isLowerBound f)) -> d2 ≤ d

  opaque
    isProp-isUpperBound : ∀ {f : I -> D} {d} -> isProp (isUpperBound f d)
    isProp-isUpperBound = isPropΠ (\_ -> isProp-≤)
    isProp-isLowerBound : ∀ {f : I -> D} {d} -> isProp (isLowerBound f d)
    isProp-isLowerBound = isPropΠ (\_ -> isProp-≤)

    isProp-isLeastUpperBound : ∀ {f : I -> D} {d} -> isProp (isLeastUpperBound f d)
    isProp-isLeastUpperBound = isProp× isProp-isUpperBound (isPropΠ (\_ -> isProp-≤))
    isProp-isGreatestLowerBound : ∀ {f : I -> D} {d} -> isProp (isGreatestLowerBound f d)
    isProp-isGreatestLowerBound = isProp× isProp-isLowerBound (isPropΠ (\_ -> isProp-≤))

    isProp-ΣisLeastUpperBound : ∀ {f : I -> D} -> isProp (Σ D (isLeastUpperBound f))
    isProp-ΣisLeastUpperBound {f = f} (d1 , ub1 , lub1) (d2 , ub2 , lub2) =
      ΣProp-path isProp-isLeastUpperBound (antisym-≤ (lub1 (d2 , ub2)) (lub2 (d1 , ub1)))
    isProp-ΣisGreatestLowerBound : ∀ {f : I -> D} -> isProp (Σ D (isGreatestLowerBound f))
    isProp-ΣisGreatestLowerBound {f = f} (d1 , lb1 , glb1) (d2 , lb2 , glb2) =
      ΣProp-path isProp-isGreatestLowerBound (antisym-≤ (glb2 (d1 , lb1)) (glb1 (d2 , lb2)))


module _ {D : Type ℓD} {D< : Rel D ℓ<} {{LO : isLinearOrder D<}} where
  isSupremum : REL (I -> D) D _
  isSupremum {I = I} f d =
    (∀ d2 -> d2 < d -> ∃[ i ∈ I ] (d2 < f i)) ×
    (∀ i d2 -> d2 < f i -> d2 < d)
  isInfimum : REL (I -> D) D _
  isInfimum {I = I} f d =
    (∀ d2 -> d < d2  -> ∃[ i ∈ I ] (f i < d2)) ×
    (∀ i d2 -> f i < d2 -> d < d2)

  opaque
    isProp-isSupremum : ∀ {f : I -> D} {d} -> isProp (isSupremum f d)
    isProp-isSupremum = isProp× (isPropΠ2 (\_ _ -> squash)) (isPropΠ3 (\_ _ _ -> isProp-<))
    isProp-isInfimum : ∀ {f : I -> D} {d} -> isProp (isInfimum f d)
    isProp-isInfimum = isProp× (isPropΠ2 (\_ _ -> squash)) (isPropΠ3 (\_ _ _ -> isProp-<))

  module _ {D≤ : Rel D ℓ≤} {{PO : isPartialOrder D≤}} {{CO : CompatibleOrderStr LO PO}} where
    opaque
      isSupremum->isUpperBound : ∀ {f : I -> D} {d} -> isSupremum f d -> isUpperBound f d
      isSupremum->isUpperBound {d = d} sup i =
        convert-≮ (\d<fi -> irrefl-< (proj₂ sup i d d<fi))
      isInfimum->isLowerBound : ∀ {f : I -> D} {d} -> isInfimum f d -> isLowerBound f d
      isInfimum->isLowerBound {d = d} inf i =
        convert-≮ (\fi<d -> irrefl-< (proj₂ inf i d fi<d))

      isSupremum->isLeastUpperBound : ∀ {f : I -> D} {d} -> isSupremum f d -> isLeastUpperBound f d
      isSupremum->isLeastUpperBound {f = f} {d} sup =
        isSupremum->isUpperBound sup ,
        (\(d2 , ub-d2) -> convert-≮ (\d2<d ->
          unsquash isPropBot (∥-map (\(i , d2<fi) -> convert-≤ (ub-d2 i) d2<fi) (proj₁ sup d2 d2<d))))
      isInfimum->isGreatestLowerBound : ∀ {f : I -> D} {d} -> isInfimum f d -> isGreatestLowerBound f d
      isInfimum->isGreatestLowerBound {f = f} {d} inf =
        isInfimum->isLowerBound inf ,
        (\(d2 , lb-d2) -> convert-≮ (\d<d2 ->
          unsquash isPropBot (∥-map (\(i , fi<d2) -> convert-≤ (lb-d2 i) fi<d2) (proj₁ inf d2 d<d2))))

  module _  where
    private
      instance
        PO = isLinearOrder->isPartialOrder-≯ LO
        CO = CompatibleNegatedLinearOrder LO

    opaque
      isProp-ΣisSupremum : ∀ {f : I -> D} -> isProp (Σ D (isSupremum f))
      isProp-ΣisSupremum (d1 , s1) (d2 , s2) =
        ΣProp-path isProp-isSupremum
          (cong fst (isProp-ΣisLeastUpperBound (d1 , (isSupremum->isLeastUpperBound s1))
                                               (d2 , (isSupremum->isLeastUpperBound s2))))
      isProp-ΣisInfimum : ∀ {f : I -> D} -> isProp (Σ D (isInfimum f))
      isProp-ΣisInfimum (d1 , s1) (d2 , s2) =
        ΣProp-path isProp-isInfimum
          (cong fst (isProp-ΣisGreatestLowerBound (d1 , (isInfimum->isGreatestLowerBound s1))
                                                  (d2 , (isInfimum->isGreatestLowerBound s2))))
