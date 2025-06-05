{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.subgroup where

open import base
open import group
open import group.inst-syntax
open import hlevel.htype

ℙ : {ℓ : Level} -> Type ℓ -> Type (ℓ-suc ℓ)
ℙ {ℓ} T = T -> hProp ℓ

_∈_ : {ℓ : Level} {A : Type ℓ} -> A -> ℙ A -> Type ℓ
a ∈ S = ⟨ S a ⟩


module _ {ℓ : Level} {D : Type ℓ} {{GS : GroupStr D}} where
  record isSubGroupStr (S : ℙ D) : Type ℓ where
    field
      ε-closed : ε ∈ S
      ∙-closed : ∀ (x y : D) -> x ∈ S -> y ∈ S -> (x ∙ y) ∈ S
      ⁻¹-closed : ∀ (x : D) -> x ∈ S -> (x ⁻¹) ∈ S


isSubGroup : {ℓ : Level} -> ((G , _) : Group ℓ) -> Pred (ℙ G) ℓ
isSubGroup (_ , GS) = isSubGroupStr {{GS = GS}}


SubGroup : {ℓ : Level} -> Group ℓ -> Type (ℓ-suc ℓ)
SubGroup G@(D , _) = Σ[ S ∈ ℙ D ] (isSubGroup G S)
