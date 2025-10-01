{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.region.scale where

open import base
open import equality-path
open import additive-group
open import apartness
open import apartness.instances.rational
open import semiring
open import hlevel.base
open import hlevel
open import hlevel.sigma
open import rational
open import sigma.base
open import truncation
open import rational-geometry.region
open import rational-geometry.point

scale-point : (k : ℚ) -> Point -> Point
scale-point k (x , y) = (k * x , k * y)

scale-point-* : ∀ k₁ k₂ p -> scale-point (k₁ * k₂) p == scale-point k₁ (scale-point k₂ p)
scale-point-* k₁ k₂ p = cong2 _,_ *-assoc *-assoc

scale-point-one : ∀ {p} -> scale-point 1# p == p
scale-point-one = cong2 _,_ *-left-one *-left-one

scale-down-region : {ℓ : Level} -> (k : ℚ) -> Region ℓ -> Region ℓ
scale-down-region {ℓ} k R = record { predicate = (\p -> Region.predicate R (scale-point k p)) }

origin-region : Region ℓ-zero
origin-region = record { predicate = \p -> P p , isProp-P p }
  where
  P : Point -> Type₀
  P (x , y) = x == 0# × y == 0#

  isProp-P : ∀ p -> isProp (P p)
  isProp-P p = isProp× (isSetℚ _ _) (isSetℚ _ _)

lift-region : {ℓ₀ : Level} -> (ℓ : Level) -> Region ℓ₀ -> Region (ℓ-max ℓ₀ ℓ)
lift-region {ℓ₀} ℓ R =
  record { predicate = \p ->
    Lift ℓ (Region.contains R p) ,
    isProp-Lift (snd (Region.predicate R p)) }


scale-up-region : {ℓ : Level} -> (k : ℚ) -> Region ℓ -> Region ℓ
scale-up-region {ℓ} k R = record { predicate = \p -> P p , squash }
  where
  P : Point -> Type ℓ
  P p₁ = ∃[ p₂ ∈ Point ] (Region.contains R p₂ × scale-point k p₂ == p₁)

scale-up-region' : {ℓ : Level} -> (k : ℚ) (k#0 : k # 0#) -> Region ℓ -> Region ℓ
scale-up-region' {ℓ} k k#0 R = record { predicate = \p -> P p , isProp-P p }
  where
  P : Point -> Type ℓ
  P p₁ = Σ[ p₂ ∈ Point ] (Region.contains R p₂ × scale-point k p₂ == p₁)

  opaque
    isProp-P : ∀ p -> isProp (P p)
    isProp-P p₀ (p₁ , P₁) (p₂ , P₂) =
      ΣProp-path (\{p} -> isProp× (snd (Region.predicate R p)) (isSet-Point _ _))
        (sym scale-point-one >=>
         (\i -> scale-point (r1/-inverse k k#0 (~ i)) p₁) >=>
         scale-point-* _ _ _ >=>
         cong (scale-point (r1/ k k#0)) (snd P₁ >=> sym (snd P₂)) >=>
         sym (scale-point-* _ _ _) >=>
         (\i -> scale-point (r1/-inverse k k#0 i) p₂) >=>
         scale-point-one)
