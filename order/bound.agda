{-# OPTIONS --cubical --safe --exact-split #-}

module order.bound where

open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import order
open import relation
open import sigma.base
open import truncation

private
  variable
    ℓI ℓD ℓ< ℓ≤ ℓ≼ : Level
    I : Type ℓI

module _ {D : Type ℓD} (D≤ : Rel D ℓ≤) where
  record isMeet (x y z : D) : Type (ℓ-max ℓ≤ ℓD) where
    constructor isMeet-cons
    field
      left : D≤ z x
      right : D≤ z y
      greatest : ∀ {z2} -> D≤ z2 x -> D≤ z2 y -> D≤ z2 z

  record isJoin (x y z : D) : Type (ℓ-max ℓ≤ ℓD) where
    constructor isJoin-cons
    field
      left : D≤ x z
      right : D≤ y z
      least : ∀ {z2} -> D≤ x z2 -> D≤ y z2 -> D≤ z z2

module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} (isProp-D≤ : ∀ {x y} -> isProp (D≤ x y)) where
  isProp-isJoin : {x y z : D} -> isProp (isJoin D≤ x y z)
  isProp-isJoin (isJoin-cons l1 r1 le1) (isJoin-cons l2 r2 le2) i =
    isJoin-cons (isProp-D≤ l1 l2 i) (isProp-D≤ r1 r2 i)
                (isPropΠ2 (\_ _ -> isProp-D≤) le1 le2 i)

  isProp-isMeet : {x y z : D} -> isProp (isMeet D≤ x y z)
  isProp-isMeet (isMeet-cons l1 r1 le1) (isMeet-cons l2 r2 le2) i =
    isMeet-cons (isProp-D≤ l1 l2 i) (isProp-D≤ r1 r2 i)
                (isPropΠ2 (\_ _ -> isProp-D≤) le1 le2 i)


module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} {{PO : isPartialOrder D≤}} where
  isMeet≤ : (x y z : D) -> Type (ℓ-max ℓ≤ ℓD)
  isMeet≤ = isMeet _≤_
  isJoin≤ : (x y z : D) -> Type (ℓ-max ℓ≤ ℓD)
  isJoin≤ = isJoin _≤_

  isProp-isJoin≤ : {x y z : D} -> isProp (isJoin D≤ x y z)
  isProp-isJoin≤ = isProp-isJoin isProp-≤
  isProp-isMeet≤ : {x y z : D} -> isProp (isMeet D≤ x y z)
  isProp-isMeet≤ = isProp-isMeet isProp-≤

  isProp-ΣisJoin≤ : {x y : D} -> isProp (Σ D (isJoin D≤ x y))
  isProp-ΣisJoin≤ (v1 , j1) (v2 , j2) =
    ΣProp-path isProp-isJoin≤
      (antisym-≤ (j1.least j2.left j2.right) (j2.least j1.left j1.right))
    where
    module j1 = isJoin j1
    module j2 = isJoin j2
  isProp-ΣisMeet≤ : {x y : D} -> isProp (Σ D (isMeet D≤ x y))
  isProp-ΣisMeet≤ (v1 , m1) (v2 , m2) =
    ΣProp-path isProp-isMeet≤
      (antisym-≤ (m2.greatest m1.left m1.right) (m1.greatest m2.left m2.right))
    where
    module m1 = isMeet m1
    module m2 = isMeet m2

module _ {D : Type ℓD} {D≼ : Rel D ℓ≼} {{PO : isPreOrder D≼}} where
  isMeet≼ : (x y z : D) -> Type (ℓ-max ℓ≼ ℓD)
  isMeet≼ = isMeet _≼_
  isJoin≼ : (x y z : D) -> Type (ℓ-max ℓ≼ ℓD)
  isJoin≼ = isJoin D≼

module _ {D : Type ℓD} {D≤ : Rel D ℓ≤} {{PO : isPartialOrder D≤}} where
  isTop≤ : Pred D (ℓ-max ℓ≤ ℓD)
  isTop≤ d = ∀ d2 -> d2 ≤ d
  isBot≤ : Pred D (ℓ-max ℓ≤ ℓD)
  isBot≤ d = ∀ d2 -> d ≤ d2

  isProp-isTop≤ : {d : D} -> isProp (isTop≤ d)
  isProp-isTop≤ = isPropΠ (\_ -> isProp-≤)
  isProp-isBot≤ : {d : D} -> isProp (isBot≤ d)
  isProp-isBot≤ = isPropΠ (\_ -> isProp-≤)

  isProp-ΣisTop≤ : isProp (Σ D isTop≤)
  isProp-ΣisTop≤ (d1 , t1) (d2 , t2) = ΣProp-path isProp-isTop≤ (antisym-≤ (t2 d1) (t1 d2))
  isProp-ΣisBot≤ : isProp (Σ D isBot≤)
  isProp-ΣisBot≤ (d1 , b1) (d2 , b2) = ΣProp-path isProp-isBot≤ (antisym-≤ (b1 d2) (b2 d1))

module _ {D : Type ℓD} {D≼ : Rel D ℓ≼} {{PO : isPreOrder D≼}} where
  isTop≼ : Pred D (ℓ-max ℓ≼ ℓD)
  isTop≼ d = ∀ d2 -> d2 ≼ d
  isBot≼ : Pred D (ℓ-max ℓ≼ ℓD)
  isBot≼ d = ∀ d2 -> d ≼ d2

module _ {D : Type ℓD} {D< : Rel D ℓ<} {{LO : isLinearOrder D<}} where
  isTop≮ : Pred D (ℓ-max ℓ< ℓD)
  isTop≮ d = ∀ d2 -> d ≮ d2
  isBot≮ : Pred D (ℓ-max ℓ< ℓD)
  isBot≮ d = ∀ d2 -> d2 ≮ d


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


module _ {ℓA ℓB ℓD ℓ< : Level} {A : Type ℓA} {B : Type ℓB} {D : Type ℓD}
         {D< : Rel D ℓ<} {{LO : isLinearOrder D<}} where
  opaque
    equiv-preserves-isSupremum : {f : B -> D} {v : D} ((g , _) : A ≃ B) ->
      isSupremum f v -> isSupremum (f ∘ g) v
    equiv-preserves-isSupremum {f} {v} (g , isEq-g) (f-close , f-above) = fg-close , fg-above
      where
      fg-close : ∀ d -> d < v -> ∃[ a ∈ A ] (d < f (g a))
      fg-close d d<v = ∥-map handle (f-close d d<v)
        where
        handle : Σ[ b ∈ B ] (d < f b) -> Σ[ a ∈ A ] (d < f (g a))
        handle (b , d<fb) = isEqInv isEq-g b , trans-<-= d<fb (cong f (sym (isEqSec isEq-g b)))

      fg-above : ∀ a d -> d < f (g a) -> d < v
      fg-above a d d<fga = f-above (g a) d d<fga

    equiv-preserves-isInfimum : {f : B -> D} {v : D} ((g , _) : A ≃ B) ->
      isInfimum f v -> isInfimum (f ∘ g) v
    equiv-preserves-isInfimum {f} {v} (g , isEq-g) (f-close , f-below) = fg-close , fg-below
      where
      fg-close : ∀ d -> v < d -> ∃[ a ∈ A ] (f (g a) < d)
      fg-close d v<d = ∥-map handle (f-close d v<d)
        where
        handle : Σ[ b ∈ B ] (f b < d) -> Σ[ a ∈ A ] (f (g a) < d)
        handle (b , fb<d) = isEqInv isEq-g b , trans-=-< (cong f (isEqSec isEq-g b)) fb<d

      fg-below : ∀ a d -> f (g a) < d -> v < d
      fg-below a d fga<d = f-below (g a) d fga<d
