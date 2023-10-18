{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.monoid where

open import base
open import cubical
open import category.base
open import category.monoidal.base
open import hlevel
open import equality-path

module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} (M : MonoidalStr C) where
  open MonoidalStrHelpers M
  open CategoryHelpers C

  record isUnital' (g : Obj C) (op : C [ g ⊗₀ g , g ]) : Type ℓM where
    field
      ε : C [ unit , g ]
      ε-left-reduce : (ε ⊗₁ id C) ⋆ op == λ⇒
      ε-right-reduce : (id C ⊗₁ ε) ⋆ op == ρ⇒

  module _ (g : Obj C) (op : C [ g ⊗₀ g , g ]) where
    isAssociative : Type ℓM
    isAssociative = α⇒ ⋆ (id C ⊗₁ op) ⋆ op == (op ⊗₁ id C) ⋆ op

  isProp-isAssociative : ∀ {g op} -> isProp (isAssociative g op)
  isProp-isAssociative = isSet-Mor C _ _


module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} {M : MonoidalStr C} where
  open MonoidalStrHelpers M
  open CategoryHelpers C

  opaque
    isProp-isUnital' : ∀ {g op} -> isProp (isUnital' M g op)
    isProp-isUnital' {g} {op}
      u₁@(record { ε = ε₁ ; ε-left-reduce = ε₁-left-reduce ; ε-right-reduce = ε₁-right-reduce })
      u₂@(record { ε = ε₂ ; ε-left-reduce = ε₂-left-reduce ; ε-right-reduce = ε₂-right-reduce }) =
      \i -> record
        { ε = ε-path i
        ; ε-left-reduce =
            isProp->PathPᵉ (\i -> isSet-Mor C (l-path i) _) ε₁-left-reduce ε₂-left-reduce i
        ; ε-right-reduce =
            isProp->PathPᵉ (\i -> isSet-Mor C (r-path i) _) ε₁-right-reduce ε₂-right-reduce i
        }

      where

      ε-path' : λ⇒ ⋆ ε₁ == λ⇒ ⋆ ε₂
      ε-path' =
        λ⇒-swap >=>
        ⋆-right (sym ε₂-left-reduce) >=>
        sym ⋆-assoc >=> ⋆-left (sym serialize₂₁ >=> serialize₁₂) >=> ⋆-assoc >=>
        ⋆-right ε₁-right-reduce >=>
        sym ρ⇒-swap >=>
        ⋆-left (sym λ⇒=ρ⇒)


      ε-path : ε₁ == ε₂
      ε-path = isEpi-λ⇒ ε-path'

      l-path : (ε₁-left-reduce i0) == (ε₂-left-reduce i0)
      l-path i = (ε-path i ⊗₁ id C) ⋆ op
      r-path : (ε₁-right-reduce i0) == (ε₂-right-reduce i0)
      r-path i = (id C ⊗₁ ε-path i) ⋆ op


module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} (M : MonoidalStr C) where
  open MonoidalStrHelpers M
  open CategoryHelpers C

  record isMonoid (g : Obj C) (op : C [ (g ⊗₀ g) , g ]) : Type ℓM where
    field
      isAssoc-op : isAssociative M g op
      isUnital-op : isUnital' M g op

    open isUnital' isUnital-op public
