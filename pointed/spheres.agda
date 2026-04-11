{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.spheres where

open import base
open import cubical
open import equality-path
open import equivalence
open import isomorphism
open import nat
open import pointed.base
open import pointed.suspension

Sⁿ∙ : Nat -> Type∙ ℓ-zero
Sⁿ∙ n = Susp∙' (iter n Susp Bot)

Sⁿ : Nat -> Type ℓ-zero
Sⁿ n = ⟨ Sⁿ∙ n ⟩

data S¹ : Type₀ where
  base : S¹
  loop : base == base

S¹∙ : Type∙ ℓ-zero
S¹∙ = S¹ , base

S¹≃Sⁿ : S¹ ≃ Sⁿ 1
S¹≃Sⁿ = isoToEquiv (iso f b fb bf)
  where
  f : S¹ -> Sⁿ 1
  f base = north
  f (loop i) = (meridian north >=> sym (meridian south)) i

  b : Sⁿ 1 -> S¹
  b north = base
  b south = base
  b (meridian north i) = loop i
  b (meridian south i) = base

  fb : ∀ x -> f (b x) == x
  fb north = refl
  fb south = (meridian south)
  fb (meridian north i) j =
    hcomp (\k -> \{ (i = i0) -> meridian north (~ k)
                  ; (i = i1) -> meridian south (~ k ∨ j)
                  ; (j = i0) -> doubleCompPath-filler (meridian north) refl (sym (meridian south)) k i
                  ; (j = i1) -> meridian north (~ k ∨ i)
                  })
      south
  fb (meridian south i) j = meridian south (i ∧ j)

  bf : ∀ x -> b (f x) == x
  bf base = refl
  bf (loop i) j = compPath-refl-right loop j i


module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  S⁰-maps-eq : (Sⁿ∙ 0 ->∙ A∙) ≃ A
  S⁰-maps-eq = isoToEquiv (iso f b fb bf)
    where

    f : (Sⁿ∙ 0 ->∙ A∙) -> A
    f g = app∙ g south
    b : A -> (Sⁿ∙ 0 ->∙ A∙)
    b a = ->∙-cons (\{ north -> ★A ; south -> a }) refl

    fb : ∀ x -> f (b x) == x
    fb _ = refl
    bf : ∀ x -> b (f x) == x
    bf (->∙-cons g p) = \i -> ->∙-cons (g' i) (\j -> p (~ i ∨ j))
      where
      g' : Path (Sⁿ 0 -> A) _ g
      g' i north = p (~ i)
      g' i south = g south

  S⁰-maps-path : (Sⁿ∙ 0 ->∙∙ A∙) == A∙
  S⁰-maps-path = Type∙-path (S⁰-maps-eq , refl)
