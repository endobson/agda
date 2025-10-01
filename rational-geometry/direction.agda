{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.direction where

open import additive-group
open import apartness
open import apartness.instances.rational
open import base
open import decision
open import discrete
open import equality-path
open import hlevel
open import hlevel.base
open import hlevel.sum
open import order
open import order.instances.rational
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational-geometry.translation
open import relation
open import semiring
open import ring
open import set-quotient
open import sum

record Direction : Type ℓ-zero where
  constructor direction
  field
    dx : ℚ
    dy : ℚ
    adx+ady=1 : abs dx + abs dy == 1#

direction-coord-path : ∀ {d₁ d₂ : Direction} ->
  Direction.dx d₁ == Direction.dx d₂ ->
  Direction.dy d₁ == Direction.dy d₂ ->
  d₁ == d₂
direction-coord-path px py = \i -> direction (px i) (py i) (pp i)
  where
  pp : PathP (\i -> abs (px i) + abs (py i) == 1#) _ _
  pp = isProp->PathP (\_ -> isSetℚ _ _)

opaque
  isSet-Direction : isSet Direction
  isSet-Direction d₁ d₂ p₁ p₂ =
    \i j -> record { dx = dx i j ; dy = dy i j ; adx+ady=1 = abs-path i j }
    where
    module d₁ = Direction d₁
    module d₂ = Direction d₂

    dx : Path (d₁.dx == d₂.dx) (cong Direction.dx p₁) (cong Direction.dx p₂)
    dx = isSetℚ (Direction.dx d₁) (Direction.dx d₂) (cong Direction.dx p₁) (cong Direction.dx p₂)
    dy : Path (d₁.dy == d₂.dy) (cong Direction.dy p₁) (cong Direction.dy p₂)
    dy = isSetℚ (Direction.dy d₁) (Direction.dy d₂) (cong Direction.dy p₁) (cong Direction.dy p₂)
    abs-path : PathP (\i -> PathP (\j -> abs (dx i j) + abs (dy i j) == 1#) d₁.adx+ady=1 d₂.adx+ady=1)
                     (cong Direction.adx+ady=1 p₁) (cong Direction.adx+ady=1 p₂)
    abs-path = isProp->PathP (\i -> isOfHLevelPathP' 1 (\_ -> isProp->isSet (isSetℚ _ _)) _ _)



reverse-direction : Direction -> Direction
reverse-direction (direction dx dy p) =
  direction (- dx) (- dy) (+-cong abs-minus abs-minus >=> p)

reverse-direction-twice : {d : Direction} ->
  reverse-direction (reverse-direction d) == d
reverse-direction-twice =
  direction-coord-path minus-double-inverse minus-double-inverse

opaque
  direction-#0 : ∀ d -> (Direction.dx d # 0#) ⊎ (Direction.dy d # 0#)
  direction-#0 (direction x y p) = handle (decide-= x 0#)
    where
    handle : Dec (x == 0#) -> (x # 0#) ⊎ (y # 0#)
    handle (no x!=0) = inj-l x!=0
    handle (yes x=0) = inj-r
      (\y=0 ->
        irrefl-path-<
          (sym +-right-zero >=>
           +-cong (sym (abs-0≤-path refl-≤) >=> cong abs (sym x=0))
                  (sym (abs-0≤-path refl-≤) >=> cong abs (sym y=0)) >=>
           p)
          0<1)


scale-direction : ℚ -> Direction -> Translation
scale-direction k (direction dx dy _) = k * dx , k * dy

scale-direction-minus : ∀ {k d} -> scale-direction (- k) d == scale-direction k (reverse-direction d)
scale-direction-minus {k} {d} =
  cong2 _,_ (minus-extract-left >=> sym minus-extract-right)
            (minus-extract-left >=> sym minus-extract-right)

scale-direction-minus' : ∀ {k d} -> scale-direction (- k) d == - (scale-direction k d)
scale-direction-minus' {k} {d} = cong2 _,_ minus-extract-left minus-extract-left


scale-direction-0# : ∀ {d} -> scale-direction 0# d == 0#
scale-direction-0# {d} = cong2 _,_ *-left-zero *-left-zero








SameSemiDirection : Rel Direction ℓ-zero
SameSemiDirection d₁ d₂ = (d₁ == d₂) ⊎ (d₁ == reverse-direction d₂)

opaque
  isProp-SameSemiDirection : ∀ {d₁ d₂} -> isProp (SameSemiDirection d₁ d₂)
  isProp-SameSemiDirection {d₁} {d₂} =
    isProp⊎ (isSet-Direction _ _) (isSet-Direction _ _) not-both
    where
    not-both : d₁ == d₂ -> d₁ == reverse-direction d₂ -> Bot
    not-both p₁ p₂ =
      either (\x#0 -> x#0 x=0) (\y#0 -> y#0 y=0) (direction-#0 d₂)
      where
      p : d₂ == reverse-direction d₂
      p = sym p₁ >=> p₂
      x y : ℚ
      x = Direction.dx d₂
      y = Direction.dy d₂

      x=0 : x == 0#
      x=0 = connected-< x≮0 0≮x
        where
        x≮0 : x ≮ 0#
        x≮0 x<0 = asym-< (minus-flips-<0 x<0) (trans-=-< (cong Direction.dx (sym p)) x<0)
        0≮x : 0# ≮ x
        0≮x 0<x = asym-< (minus-flips-0< 0<x) (trans-<-= 0<x (cong Direction.dx p))

      y=0 : y == 0#
      y=0 = connected-< y≮0 0≮y
        where
        y≮0 : y ≮ 0#
        y≮0 y<0 = asym-< (minus-flips-<0 y<0) (trans-=-< (cong Direction.dy (sym p)) y<0)
        0≮y : 0# ≮ y
        0≮y 0<y = asym-< (minus-flips-0< 0<y) (trans-<-= 0<y (cong Direction.dy p))


sym-SameSemiDirection : Symmetric SameSemiDirection
sym-SameSemiDirection (inj-l p) = inj-l (sym p)
sym-SameSemiDirection (inj-r p) =
  inj-r (sym reverse-direction-twice >=> cong reverse-direction (sym p))

SemiDirection : Type ℓ-zero
SemiDirection = Direction / SameSemiDirection

isSet-SemiDirection : isSet SemiDirection
isSet-SemiDirection = squash/
