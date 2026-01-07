{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.box where

open import additive-group
open import base
open import equality-path
open import hlevel
open import hlevel.base
open import hlevel.sigma
open import order
open import order.instances.rational
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational-geometry.point
open import rational-geometry.region
open import semiring

record Box : Type₀ where
  field
    left : ℚ
    right : ℚ
    bottom : ℚ
    top : ℚ
    left<right : left < right
    bottom<top : bottom < top

  region : Region ℓ-zero
  region = record { predicate = \x -> P x , isProp-P x }
    where
    P : Point -> Type₀
    P (x , y) = (left ≤ x) × (x < right) × (bottom ≤ y) × (y < top)

    opaque
      isProp-P : (x : Point) -> isProp (P x)
      isProp-P x = isProp× isProp-≤ (isProp× isProp-< (isProp× isProp-≤ isProp-<))

  contains : Pred Point ℓ-zero
  contains = Region.contains region

  area : ℚ
  area = (diff left right) * (diff bottom top)

  opaque
    0<area : 0# < area
    0<area = *-preserves-0< (diff-0<⁺ left<right) (diff-0<⁺ bottom<top)

  bottom-left : Point
  bottom-left = left , bottom

  opaque
    bottom-left∈region : Region.contains region bottom-left
    bottom-left∈region = refl-≤ , left<right , refl-≤ , bottom<top

opaque
  isSet-Box : isSet Box
  isSet-Box b₁ b₂ p₁ p₂ = \i j -> record
    { left = left-path i j
    ; right = right-path i j
    ; bottom = bottom-path i j
    ; top = top-path i j
    ; left<right = lr-path i j
    ; bottom<top = bt-path i j
    }
    where
    left-path : cong Box.left p₁ == cong Box.left p₂
    left-path = isSetℚ (Box.left b₁) (Box.left b₂) (cong Box.left p₁) (cong Box.left p₂)
    right-path : cong Box.right p₁ == cong Box.right p₂
    right-path = isSetℚ (Box.right b₁) (Box.right b₂) (cong Box.right p₁) (cong Box.right p₂)
    lr-path : PathP (\i -> PathP (\j -> left-path i j < right-path i j)
                                 (Box.left<right b₁) (Box.left<right b₂))
                    (cong Box.left<right p₁)
                    (cong Box.left<right p₂)
    lr-path = isProp->PathP (\i -> isOfHLevelPathP' 1 (\j -> isProp->isSet isProp-<) _ _)
    bottom-path : cong Box.bottom p₁ == cong Box.bottom p₂
    bottom-path = isSetℚ (Box.bottom b₁) (Box.bottom b₂) (cong Box.bottom p₁) (cong Box.bottom p₂)
    top-path : cong Box.top p₁ == cong Box.top p₂
    top-path = isSetℚ (Box.top b₁) (Box.top b₂) (cong Box.top p₁) (cong Box.top p₂)
    bt-path : PathP (\i -> PathP (\j -> bottom-path i j < top-path i j)
                                 (Box.bottom<top b₁) (Box.bottom<top b₂))
                    (cong Box.bottom<top p₁)
                    (cong Box.bottom<top p₂)
    bt-path = isProp->PathP (\i -> isOfHLevelPathP' 1 (\j -> isProp->isSet isProp-<) _ _)

opaque
  Box-coord-path : (b₁ b₂ : Box) ->
    Box.left b₁ == Box.left b₂ ->
    Box.right b₁ == Box.right b₂ ->
    Box.bottom b₁ == Box.bottom b₂ ->
    Box.top b₁ == Box.top b₂ ->
    b₁ == b₂
  Box-coord-path b₁ b₂ l-path r-path b-path t-path = \i -> record
    { left = l-path i
    ; right = r-path i
    ; bottom = b-path i
    ; top = t-path i
    ; left<right = lr-path i
    ; bottom<top = bt-path i
    }
    where
    lr-path : PathP (\i -> l-path i < r-path i) (Box.left<right b₁) (Box.left<right b₂)
    lr-path = isProp->PathP (\i -> isProp-<)
    bt-path : PathP (\i -> b-path i < t-path i) (Box.bottom<top b₁) (Box.bottom<top b₂)
    bt-path = isProp->PathP (\i -> isProp-<)


opaque
  Box-region-path : (b₁ b₂ : Box) -> Box.region b₁ == Box.region b₂ -> b₁ == b₂
  Box-region-path b₁ b₂ r-path =
    Box-coord-path b₁ b₂ left-path right-path bottom-path top-path
    where

    module _
      (b₁ : Box) (b₂ : Box) (r-path : Box.region b₁ == Box.region b₂)
      (left-path : Box.left b₁ == Box.left b₂)
      (bottom-path : Box.bottom b₁ == Box.bottom b₂)
      where
      private
        module b₁ = Box b₁
        module b₂ = Box b₂

        p : Point
        p = b₁.right , b₁.bottom

        ¬p∈b₁ : ¬ (Region.contains b₁.region p)
        ¬p∈b₁ (_ , r<r , _ , _) = irrefl-< r<r


      r₁≮r₂ : b₁.right ≮ b₂.right
      r₁≮r₂ r₁<r₂ = ¬p∈b₁ (transport (\i -> Region.contains (r-path (~ i)) p) p∈b₂)
        where
        p∈b₂ : Region.contains b₂.region p
        p∈b₂ = trans-=-≤ (sym left-path) (weaken-< b₁.left<right) , r₁<r₂ ,
               path-≤ (sym bottom-path) , (trans-=-< bottom-path b₂.bottom<top)

    module _
      (b₁ : Box) (b₂ : Box) (r-path : Box.region b₁ == Box.region b₂)
      (left-path : Box.left b₁ == Box.left b₂)
      (bottom-path : Box.bottom b₁ == Box.bottom b₂)
      where
      private
        module b₁ = Box b₁
        module b₂ = Box b₂

        p : Point
        p = b₁.left , b₁.top

        ¬p∈b₁ : ¬ (Region.contains b₁.region p)
        ¬p∈b₁ (_ , _ , _ , t<t) = irrefl-< t<t


      t₁≮t₂ : b₁.top ≮ b₂.top
      t₁≮t₂ t₁<t₂ = ¬p∈b₁ (transport (\i -> Region.contains (r-path (~ i)) p) p∈b₂)
        where
        p∈b₂ : Region.contains b₂.region p
        p∈b₂ = path-≤ (sym left-path) , (trans-=-< left-path b₂.left<right) ,
               trans-=-≤ (sym bottom-path) (weaken-< b₁.bottom<top) , t₁<t₂



    module _ where
      private
        module b₁ = Box b₁
        module b₂ = Box b₂

        p₁ : Point
        p₁ = b₁.left , b₁.bottom
        p₂ : Point
        p₂ = b₂.left , b₂.bottom

        p₁∈b₁ : Region.contains b₁.region p₁
        p₁∈b₁ = refl-≤ , b₁.left<right , refl-≤ , b₁.bottom<top
        p₂∈b₂ : Region.contains b₂.region p₂
        p₂∈b₂ = refl-≤ , b₂.left<right , refl-≤ , b₂.bottom<top

        p₁∈b₂ : Region.contains b₂.region p₁
        p₁∈b₂ = transport (\i -> Region.contains (r-path i) p₁) p₁∈b₁
        p₂∈b₁ : Region.contains b₁.region p₂
        p₂∈b₁ = transport (\i -> Region.contains (r-path (~ i)) p₂) p₂∈b₂

      left-path : b₁.left == b₂.left
      left-path = antisym-≤ (fst p₂∈b₁) (fst p₁∈b₂)
      bottom-path : b₁.bottom == b₂.bottom
      bottom-path = antisym-≤ (fst (snd (snd p₂∈b₁))) (fst (snd (snd p₁∈b₂)))

      right-path : b₁.right == b₂.right
      right-path = connected-< (r₁≮r₂ b₁ b₂ r-path left-path bottom-path)
                               (r₁≮r₂ b₂ b₁ (sym r-path) (sym left-path) (sym bottom-path))
      top-path : b₁.top == b₂.top
      top-path = connected-< (t₁≮t₂ b₁ b₂ r-path left-path bottom-path)
                             (t₁≮t₂ b₂ b₁ (sym r-path) (sym left-path) (sym bottom-path))
