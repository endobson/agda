{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.big-o.arithmetic where

open import additive-group
open import base
open import equality
open import order
open import order.minmax
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.big-o
open import relation
open import semiring
open import subset.subspace
open import truncation

module _ {ℓI ℓD ℓI≤ ℓI< ℓD≤ ℓD< : Level} {I : Type ℓI} {D : Type ℓD}
         {I≤ : Rel I ℓI≤} {I< : Rel I ℓI<} {D≤ : Rel D ℓD≤} {D< : Rel D ℓD<}
         {{IPO : isPartialOrder I≤}} {{ILO : isLinearOrder I<}}
         {{DPO : isPartialOrder D≤}} {DLO : isLinearOrder D<}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
         {{AG : AdditiveGroup ACM}}
         {{D-Max : MaxOperationStr DLO}}
         {{I-Max : MaxOperationStr ILO}}
         {{LOA : LinearlyOrderedAdditiveStr ACM DLO}}
         {{POA : PartiallyOrderedAdditiveStr ACM DPO}}
         {{ICO : CompatibleOrderStr ILO IPO}}
         {{DCO : CompatibleOrderStr DLO DPO}}
         {{LOS : LinearlyOrderedSemiringStr S DLO}} where
  private
    instance
      I-DLO = DLO
      I-S = S
      I-ACM = ACM

  opaque
    BigO-+ : {f1 f2 g : I -> D} -> BigO f1 g -> BigO f2 g -> BigO (\i -> f1 i + f2 i) g
    BigO-+ {f1} {f2} {g} = ∥-map2 handle
      where
      handle : BigO' f1 g -> BigO' f2 g -> BigO' (\i -> f1 i + f2 i) g
      handle ((k1 , 0<k1) , N1 , b1) ((k2 , 0<k2) , N2 , b2) =
        (k1 + k2 , +-preserves-0< 0<k1 0<k2) , max N1 N2 , bound
        where
        bound : (i : I) -> max N1 N2 ≤ i -> abs (f1 i + f2 i) ≤ ((k1 + k2) * g i)
        bound i N≤i =
          trans-≤ abs-distrib-+
            (trans-≤-= (+-preserves-≤ (b1 i (trans-≤ max-≤-left N≤i)) (b2 i (trans-≤ max-≤-right N≤i)))
                       (sym *-distrib-+-right))

  module _
    {{POA : PartiallyOrderedSemiringStr S DPO}}
    {{SLOS : StronglyLinearlyOrderedSemiringStr S DLO}} where
    opaque
      BigO-* : {f1 f2 g1 g2 : I -> D} ->
        BigO f1 g1 -> BigO f2 g2 -> BigO (\i -> f1 i * f2 i) (\i -> g1 i * g2 i)
      BigO-* {f1} {f2} {g1} {g2} = ∥-map2 handle
        where
        handle : BigO' f1 g1 -> BigO' f2 g2 -> BigO' (\i -> f1 i * f2 i) (\i -> g1 i * g2 i)
        handle ((k1 , 0<k1) , N1 , b1) ((k2 , 0<k2) , N2 , b2) =
          (k1 * k2 , *-preserves-0< 0<k1 0<k2) , max N1 N2 , bound
          where
          bound : (i : I) -> max N1 N2 ≤ i -> abs (f1 i * f2 i) ≤ ((k1 * k2) * (g1 i * g2 i))
          bound i N≤i =
            trans-=-≤ abs-distrib-*
              (trans-≤-= (trans-≤ (*₁-preserves-≤ abs-0≤ (b2 i (trans-≤ max-≤-right N≤i)))
                                  (*₂-preserves-≤ (b1 i (trans-≤ max-≤-left N≤i)) 0≤k2g2))
                *-swap)
            where
            0≤k2g2 : 0# ≤ (k2 * g2 i)
            0≤k2g2 = trans-≤ abs-0≤ (b2 i (trans-≤ max-≤-right N≤i))
