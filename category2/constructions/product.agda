{-# OPTIONS --cubical --safe --exact-split #-}

module category2.constructions.product where

open import base
open import equality-path
open import hlevel.base
open import category2.base

module _ {ℓO₁ ℓM₁ ℓO₂ ℓM₂}
  (C₁@(category O₁ M₁ _) : Category ℓO₁ ℓM₁)
  (C₂@(category O₂ M₂ _) : Category ℓO₂ ℓM₂)
  where
  private
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂


  module _ ((x₁ , x₂) (y₁ , y₂) : O₁ × O₂) where
    record ProdC→ : Type (ℓ-max ℓM₁ ℓM₂) where
      constructor _,_
      field
        m₁ : M₁ x₁ y₁
        m₂ : M₂ x₂ y₂



module _ {ℓO₁ ℓM₁ ℓO₂ ℓM₂}
  {C₁@(category O₁ M₁ _) : Category ℓO₁ ℓM₁}
  {C₂@(category O₂ M₂ _) : Category ℓO₂ ℓM₂}
  where
  private
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂

  private
    isSet-ProdC→ : ∀ {x y} -> isSet (ProdC→ C₁ C₂ x y)
    isSet-ProdC→ (f₁ , g₁) (f₂ , g₂) p₁ p₂ i j =
      isSet-Mor f₁ f₂ (cong ProdC→.m₁ p₁) (cong ProdC→.m₁ p₂) i j ,
      isSet-Mor g₁ g₂ (cong ProdC→.m₂ p₁) (cong ProdC→.m₂ p₂) i j


  instance
    Prod-CategoryStr : CategoryStr (ProdC→ C₁ C₂)
    Prod-CategoryStr = record
      { id = id , id
      ; _⋆_ = \ (l₁ , l₂) (r₁ , r₂) -> (l₁ ⋆ r₁ , l₂ ⋆ r₂)
      ; ⋆-left-idᵉ = \ (m₁ , m₂) i -> ⋆-left-idᵉ m₁ i , ⋆-left-idᵉ m₂ i
      ; ⋆-right-idᵉ = \ (m₁ , m₂) i -> ⋆-right-idᵉ m₁ i , ⋆-right-idᵉ m₂ i
      ; ⋆-assocᵉ = \ (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) i -> ⋆-assocᵉ f₁ g₁ h₁ i , ⋆-assocᵉ f₂ g₂ h₂ i
      ; isSet-Mor = isSet-ProdC→
      }

module _ {ℓO₁ ℓM₁ ℓO₂ ℓM₂}
  (C₁@(category O₁ M₁ _) : Category ℓO₁ ℓM₁)
  (C₂@(category O₂ M₂ _) : Category ℓO₂ ℓM₂)
  where

  ProdC : Category (ℓ-max ℓO₁ ℓO₂) (ℓ-max ℓM₁ ℓM₂)
  ProdC = record
    { Obj = O₁ × O₂
    ; Mor = ProdC→ C₁ C₂
    ; Str = Prod-CategoryStr
    }
