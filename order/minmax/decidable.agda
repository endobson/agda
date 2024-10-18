{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax.decidable where

open import base
open import functions
open import order
open import order.minmax
open import relation


module _ {ℓD ℓ< : Level} (D : Type ℓD) {D< : Rel D ℓ<}
         {LO : isLinearOrder D<} {{DLO : DecidableLinearOrderStr LO}}
  where
  private
    instance
      ILO = LO

    opaque
      minmax-tri : (d1 d2 : D) -> Tri< d1 d2 -> (Σ D (isMin d1 d2)) × (Σ D (isMax d1 d2))
      minmax-tri d1 d2 (tri< d1<d2 _ d2≮d1) = (d1 , min') , (d2 , max')
        where
        min' : isMin d1 d2 d1
        min' .isMin.left  = irrefl-<
        min' .isMin.right = d2≮d1
        min' .isMin.greatest d1<d d2<d = d1<d
        max' : isMax d1 d2 d2
        max' .isMax.left  = d2≮d1
        max' .isMax.right = irrefl-<
        max' .isMax.least d1<d d2<d = d2<d
      minmax-tri d1 d2 (tri= d1≮d2 d1=d2 d2≮d1) = (d1 , min') , (d2 , max')
        where
        min' : isMin d1 d2 d1
        min' .isMin.left  = irrefl-<
        min' .isMin.right = d2≮d1
        min' .isMin.greatest d1<d d2<d = d1<d
        max' : isMax d1 d2 d2
        max' .isMax.left  = d2≮d1
        max' .isMax.right = irrefl-<
        max' .isMax.least d1<d d2<d = d2<d
      minmax-tri d1 d2 (tri> d1≮d2 _ d2<d1) = (d2 , min') , (d1 , max')
        where
        min' : isMin d1 d2 d2
        min' .isMin.left  = d1≮d2
        min' .isMin.right = irrefl-<
        min' .isMin.greatest d1<d d2<d = d2<d
        max' : isMax d1 d2 d1
        max' .isMax.left  = irrefl-<
        max' .isMax.right = d1≮d2
        max' .isMax.least d1<d d2<d = d1<d

      min' : (d1 d2 : D) -> (Σ D (isMin d1 d2))
      min' d1 d2 = proj₁ (minmax-tri d1 d2 (trichotomous-< d1 d2))

      max' : (d1 d2 : D) -> (Σ D (isMax d1 d2))
      max' d1 d2 = proj₂ (minmax-tri d1 d2 (trichotomous-< d1 d2))

  opaque
    MinOperationStr-Decidable : MinOperationStr LO
    MinOperationStr-Decidable = isMin->MinOperationStr min'

    MaxOperationStr-Decidable : MaxOperationStr LO
    MaxOperationStr-Decidable = isMax->MaxOperationStr max'
