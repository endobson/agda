{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.base where

open import base
open import equality
open import category.base
open import fin-algebra
open import category.constructions.product
open import category.constructions.power

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (⊗ : BiFunctor C C C) where
  private
    module C = PreCategory C
    module ⊗ = Functor ⊗

    _⊗₀_ : C.Obj -> C.Obj -> C.Obj
    c1 ⊗₀ c2 = ⊗.obj (c1 , c2)

    _⊗₁_ : {x y z w : C.Obj} -> C [ x , y ] -> C [ z , w ] -> C [ (x ⊗₀ z) , (y ⊗₀ w) ]
    f ⊗₁ g = ⊗.mor (f , g)

    i0 : FinT 3
    i0 = inj-l tt
    i1 : FinT 3
    i1 = inj-r (inj-l tt)
    i2 : FinT 3
    i2 = inj-r (inj-r (inj-l tt))

  LeftBiasedDoubleApplicationFunctor : Functor (PowerCat C 3) C
  LeftBiasedDoubleApplicationFunctor = record
    { obj = \os -> (os i0 ⊗₀ os i1) ⊗₀ os i2
    ; mor = \ms -> (ms i0 ⊗₁ ms i1) ⊗₁ ms i2
    ; id = \_ -> cong (_⊗₁ id C) (⊗.id _) >=> (⊗.id _)
    ; ⋆ = \f g -> cong (_⊗₁ _) (⊗.⋆ _ _) >=> (⊗.⋆ _ _)
    }

  RightBiasedDoubleApplicationFunctor : Functor (PowerCat C 3) C
  RightBiasedDoubleApplicationFunctor = record
    { obj = \os -> os i0 ⊗₀ (os i1 ⊗₀ os i2)
    ; mor = \ms -> ms i0 ⊗₁ (ms i1 ⊗₁ ms i2)
    ; id = \_ -> cong (id C ⊗₁_) (⊗.id _) >=> (⊗.id _)
    ; ⋆ = \f g -> cong (_ ⊗₁_) (⊗.⋆ _ _) >=> (⊗.⋆ _ _)
    }


module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  private
    module C = PreCategory C
  record MonoidalStr : Type (ℓ-max ℓO ℓM) where
    field
      ⊗ : BiFunctor C C C
      unit : Obj C
      unitorˡ : NaturalIsomorphism (appˡ ⊗ unit) (idF C)
      unitorʳ : NaturalIsomorphism (appʳ ⊗ unit) (idF C)
      associator : NaturalIsomorphism (LeftBiasedDoubleApplicationFunctor ⊗)
                                      (RightBiasedDoubleApplicationFunctor ⊗)
