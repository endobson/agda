{-# OPTIONS --cubical --safe --exact-split #-}

module category2.pullback where


open import base
open import truncation
open import category2.base

module _ {ℓO ℓM : Level} {O : Type ℓO} {M : O -> O -> Type ℓM}
         {{CS : CategoryStr M}} where

  isPullback : {a b c : O}
    (f : M a c) (g : M b c)
    (p : O) (π₁ : M p a) (π₂ : M p b) -> Type _
  isPullback {a} {b} f g p π₁ π₂ =
    π₁ ⋆ f == π₂ ⋆ g ×
    ∀ {q : O} (φ₁ : M q a) (φ₂ : M q b) -> (φ₁ ⋆ f == φ₂ ⋆ g) ->
      ∃![ θ ∈ M q p ] (θ ⋆ π₁ == φ₁ × θ ⋆ π₂ == φ₂)


  record Pullback {o₁ o₂ o₃ : O} (f : M o₁ o₃) (g : M o₂ o₃) : Type (ℓ-max ℓO ℓM)
    where
    field
      obj : O
      π₁ : M obj o₁
      π₂ : M obj o₂
      is-pullback : isPullback f g obj π₁ π₂


module _ {ℓO ℓM : Level} (C : Category ℓO ℓM) where
  Pullback▪ : {o₁ o₂ o₃ : Obj C} (f : C →[ o₁ , o₃ ]) (g : C →[ o₂ , o₃ ]) -> Type (ℓ-max ℓO ℓM)
  Pullback▪ = Pullback {{CS = Category.Str C}}
