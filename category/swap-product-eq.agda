{-# OPTIONS --cubical --safe --exact-split #-}

module category.swap-product-eq where

open import base
open import category.adjunction
open import category.base
open import category.constructions.product
open import category.functor
open import equality

private
  module _ {ℓOC ℓMC ℓOD ℓMD : Level}
           (C : PreCategory ℓOC ℓMC) (D : PreCategory ℓOD ℓMD) where

    swap-F : Functor (ProductCat C D) (ProductCat D C)
    swap-F = record
      { obj = \ (c , d) -> d , c
      ; mor = \ (f , g) -> g , f
      ; id = \_ -> refl
      ; ⋆ = \_ _ -> refl
      }

module _ {ℓOC ℓMC ℓOD ℓMD : Level}
         (C : PreCategory ℓOC ℓMC) (D : PreCategory ℓOD ℓMD) where
  private
    CD : PreCategory (ℓ-max ℓOC ℓOD) (ℓ-max ℓMC ℓMD)
    CD = ProductCat C D
    DC : PreCategory (ℓ-max ℓOC ℓOD) (ℓ-max ℓMC ℓMD)
    DC = ProductCat D C

    module CD = CategoryHelpers CD
    module DC = CategoryHelpers DC

  swap-Adj : Adjunction (swap-F C D) (swap-F D C)
  swap-Adj = record
    { unit = record
      { obj = \_ -> id CD
      ; mor = \m -> CD.⋆-left-id >=> sym CD.⋆-right-id
      }
    ; counit = record
      { obj = \_ -> id DC
      ; mor = \m -> DC.⋆-left-id >=> sym DC.⋆-right-id
      }
    ; tri-L = \_ -> DC.⋆-id²
    ; tri-R = \_ -> CD.⋆-id²
    }

  swap-AdjEq : AdjointEquiv (swap-F C D) (swap-F D C)
  swap-AdjEq = swap-Adj ,
    (\ _ -> record
       { inv = id CD
       ; sec = CD.⋆-id²
       ; ret = CD.⋆-id²
       }) ,
    (\ _ -> record
       { inv = id DC
       ; sec = DC.⋆-id²
       ; ret = DC.⋆-id²
       })
