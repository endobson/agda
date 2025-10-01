{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.translation where

open import additive-group
open import base
open import semiring
open import equality-path
open import hlevel.base
open import rational
open import rational-geometry.point

record Translation : Type₀ where
  constructor _,_
  field
    dx : ℚ
    dy : ℚ

isSet-Translation : isSet Translation
isSet-Translation (dx₁ , dy₁) (dx₂ , dy₂) p₁ p₂ i j =
  isSetℚ dx₁ dx₂ (cong Translation.dx p₁) (cong Translation.dx p₂) i j ,
  isSetℚ dy₁ dy₂ (cong Translation.dy p₁) (cong Translation.dy p₂) i j


private
  t+ : Translation -> Translation -> Translation
  t+ (dx₁ , dy₁) (dx₂ , dy₂) = dx₁ + dx₂ , dy₁ + dy₂

  t- : Translation -> Translation
  t- (dx₁ , dy₁) = - dx₁ , - dy₁

  zero-translation : Translation
  zero-translation = 0# , 0#

instance
  AdditiveCommMonoid-Translation : AdditiveCommMonoid Translation
  AdditiveCommMonoid-Translation = record
    { comm-monoid = record
      { monoid = record
        { _∙_ = t+
        ; ε = zero-translation
        ; ∙-assoc = cong2 _,_ +-assoc +-assoc
        ; ∙-left-ε = cong2 _,_ +-left-zero +-left-zero
        ; ∙-right-ε = cong2 _,_ +-right-zero +-right-zero
        ; isSet-Domain = isSet-Translation
        }
      ; ∙-commute = cong2 _,_ +-commute +-commute
      }
    }

  AdditiveGroup-Translation : AdditiveGroup AdditiveCommMonoid-Translation
  AdditiveGroup-Translation = record
    { -_ = t-
    ; +-inverse = cong2 _,_ +-inverse +-inverse
    }


shift-point : Translation -> Point -> Point
shift-point (dx , dy) (x , y) = x + dx , y + dy

point-shift : Point -> Translation -> Point
point-shift p t = shift-point t p

shift-point-+ : ∀ {t₁ t₂ p} -> shift-point (t₁ + t₂) p == shift-point t₁ (shift-point t₂ p)
shift-point-+ = cong2 _,_ (+-right +-commute >=> sym +-assoc) (+-right +-commute >=> sym +-assoc)

shift-point-zero : ∀ {p} -> shift-point 0# p == p
shift-point-zero = cong2 _,_ +-right-zero +-right-zero

shift-point-swap : ∀ {t p₁ p₂} -> shift-point t p₁ == p₂ -> shift-point (- t) p₂ == p₁
shift-point-swap {t} {p₁} path =
  cong (shift-point (- t)) (sym path) >=>
  sym shift-point-+ >=>
  cong (\t -> shift-point t p₁) (+-commute >=> +-inverse) >=>
  shift-point-zero

scale-translation : ℚ -> Translation -> Translation
scale-translation k (dx , dy) = k * dx , k * dy
