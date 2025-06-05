{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.spheres where

open import base
open import sigma
open import pointed.base
open import pointed.suspension
open import nat
open import equivalence
open import cubical
open import univalence
open import isomorphism
open import equality-path

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
  fb (meridian north i) = (\j -> p2 j i)
    where
    p : PathP (\i -> north == meridian south i)
              (meridian north >=> sym (meridian south))
              (meridian north >=> refl)
    p i = meridian north >=> (\j -> meridian south (~ j ∨ i))

    p2 : PathP (\i -> north == meridian south i)
          (meridian north >=> sym (meridian south)) (meridian north)
    p2 = transP-left p (compPath-refl-right (meridian north))
  fb (meridian south i) = (\j -> p j i)
    where
    p : PathP (\i -> north == meridian south i)
          refl (meridian south)
    p i j = meridian south (i ∧ j)

  bf : ∀ x -> b (f x) == x
  bf base = refl
  bf (loop i) = (\j -> p j i)
    where
    p : (loop >=> refl) == loop
    p = compPath-refl-right loop


module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  -- TODO make this nicer
  S⁰-maps-path : (Sⁿ∙ 0 ->∙∙ A∙) == A∙
  S⁰-maps-path =
    sigmaPath->pathSigma _ _ (isoToPath iso₁ , trans-path)
    where

    f : (Sⁿ∙ 0 ->∙ A∙) -> A
    f g = app∙ g south
    b : A -> (Sⁿ∙ 0 ->∙ A∙)
    b a = ->∙-cons (\{ north -> ★A ; south -> a }) refl

    fb : ∀ x -> f (b x) == x
    fb _ = refl
    bf : ∀ x -> b (f x) == x
    bf (->∙-cons g p) = \i -> ->∙-cons (g' i) (p' i)
      where
      g' : Path (Sⁿ 0 -> A) _ g
      g' i north = p (~ i)
      g' i south = g south

      p' : PathP (\i -> g' i north == ★A) refl p
      p' i j = p (~ i ∨ j)


    iso₁ : Iso (Sⁿ∙ 0 ->∙ A∙) A
    iso₁ = iso f b fb bf

    trans-path : (transport (isoToPath iso₁) (->∙-cons (\_ -> ★A) refl)) == ★A
    trans-path i = transport-isoToPath iso₁ i (->∙-cons (\_ -> ★A) refl)
