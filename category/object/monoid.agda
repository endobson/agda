{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.monoid where

open import base
open import cubical
open import category.base
open import category.monoidal.base
open import hlevel
open import equality-path

module _ {ℓO ℓM} ((C , M) : MonoidalCategory ℓO ℓM) where
  open MonoidalStrHelpers M

  record Magma : Type (ℓ-max ℓO ℓM) where
    constructor magma
    field
      obj : Obj C
      op : C [ obj ⊗₀ obj , obj ]

  magmaᵉ : (obj : Obj C) -> C [ obj ⊗₀ obj , obj ] -> Magma
  magmaᵉ = magma

module _ {ℓO ℓM} {MC@(C , M) : MonoidalCategory ℓO ℓM} ((magma g op) : Magma MC) where
  open MonoidalStrHelpers M
  open CategoryHelpers C

  record isUnital : Type ℓM where
    field
      ε : C [ unit , g ]
      ε-left-reduce' : (ε ⊗₁ id C) ⋆ op == λ⇒
      ε-right-reduce' : (id C ⊗₁ ε) ⋆ op == ρ⇒


  record isAssociative : Type ℓM where
    field
      op-assoc : α⇒ ⋆ (id C ⊗₁ op) ⋆ op == (op ⊗₁ id C) ⋆ op

module _ {ℓO ℓM} {MC@(C , M) : MonoidalCategory ℓO ℓM} where
  open MonoidalStrHelpers M
  open CategoryHelpers C

  opaque
    isProp-isAssociative : ∀ {m : Magma MC} -> isProp (isAssociative m)
    isProp-isAssociative {magma g op}
      a₁@(record { op-assoc = op-assoc₁ })
      a₂@(record { op-assoc = op-assoc₂ }) =
      \i -> record { op-assoc = isSet-Mor C _ _ op-assoc₁ op-assoc₂ i }

    isProp-isUnital : ∀ {m : Magma MC} -> isProp (isUnital m)
    isProp-isUnital {magma g op}
      u₁@(record { ε = ε₁ ; ε-left-reduce' = ε₁-left-reduce' ; ε-right-reduce' = ε₁-right-reduce' })
      u₂@(record { ε = ε₂ ; ε-left-reduce' = ε₂-left-reduce' ; ε-right-reduce' = ε₂-right-reduce' }) =
      \i -> record
        { ε = ε-path i
        ; ε-left-reduce' =
            isProp->PathPᵉ (\i -> isSet-Mor C (l-path i) _) ε₁-left-reduce' ε₂-left-reduce' i
        ; ε-right-reduce' =
            isProp->PathPᵉ (\i -> isSet-Mor C (r-path i) _) ε₁-right-reduce' ε₂-right-reduce' i
        }

      where

      ε-path' : λ⇒ ⋆ ε₁ == λ⇒ ⋆ ε₂
      ε-path' =
        λ⇒-swap >=>
        ⋆-right (sym ε₂-left-reduce') >=>
        sym ⋆-assoc >=> ⋆-left (sym serialize₂₁ >=> serialize₁₂) >=> ⋆-assoc >=>
        ⋆-right ε₁-right-reduce' >=>
        sym ρ⇒-swap >=>
        ⋆-left (sym λ⇒=ρ⇒)


      ε-path : ε₁ == ε₂
      ε-path = isEpi-λ⇒ ε-path'

      l-path : (ε₁-left-reduce' i0) == (ε₂-left-reduce' i0)
      l-path i = (ε-path i ⊗₁ id C) ⋆ op
      r-path : (ε₁-right-reduce' i0) == (ε₂-right-reduce' i0)
      r-path i = (id C ⊗₁ ε-path i) ⋆ op

module _ {ℓO ℓM} {MC : MonoidalCategory ℓO ℓM} where
  record isMonoid (m : Magma MC)  : Type ℓM where
    field
      isAssociative-magma : isAssociative m
      isUnital-magma : isUnital m

    open isUnital isUnital-magma public
    open isAssociative isAssociative-magma public
