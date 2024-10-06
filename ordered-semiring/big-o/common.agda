{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.big-o.common where

open import additive-group
open import base
open import equality
open import functions
open import inhabited
open import order
open import order.bound
open import order.minmax
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-semiring
open import ordered-semiring.big-o
open import relation
open import semiring
open import subset.subspace
open import truncation

module _ {ℓI ℓD ℓI≤ ℓD≤ ℓD< : Level} {I : Type ℓI} {D : Type ℓD}
         {I≤ : Rel I ℓI≤} {D≤ : Rel D ℓD≤} {D< : Rel D ℓD<}
         {{IPO : isPartialOrder I≤}}
         {{DPO : isPartialOrder D≤}} {DLO : isLinearOrder D<}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
         {{AG : AdditiveGroup ACM}}
         {{D-Max : MaxOperationStr DLO}} where
  private
    instance
      I-DLO = DLO
      I-S = S
      I-ACM = ACM

  module _ {{In-I : InhabitedStr I}}
           {LOS : LinearlyOrderedSemiringStr S DLO}
           {{NTLOS : NonTrivialLinearlyOrderedSemiringStr LOS}} where
    opaque
      BigO-abs : {f : I -> D} -> BigO f (abs ∘ f)
      BigO-abs = ∥-map (\i -> (1# , 0<1) , i , (\_ _ -> path-≤ (sym *-left-one))) (inhabitedᵉ I)

  module _ {{In-I : InhabitedStr I}}
           {{LOA : LinearlyOrderedAdditiveStr ACM DLO}}
           {{POA : PartiallyOrderedAdditiveStr ACM DPO}}
           {{LOS : LinearlyOrderedSemiringStr S DLO}}
           {{NTLOS : NonTrivialLinearlyOrderedSemiringStr LOS}}
           {{DCO : CompatibleOrderStr DLO DPO}}
           where
    opaque
      BigO-Bounded : {f : I -> D} {d : D} -> isUpperBound (abs ∘ f) d -> BigO f (\_ -> 1#)
      BigO-Bounded {f} {d} ub-d = ∥-map handle (inhabitedᵉ I)
        where
        handle : (i : I) -> BigO' f (\_ -> 1#)
        handle i =
          ((d + 1#) , 0<d+1) , i ,
          (\i2 _ -> trans-≤-= (trans-≤ (ub-d i2) (weaken-< d<d+1)) (sym *-right-one))
          where
          d<d+1 : d < (d + 1#)
          d<d+1 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1)
          0<d+1 : 0# < (d + 1#)
          0<d+1 = trans-≤-< (trans-≤ abs-0≤ (ub-d i)) d<d+1

  module _ {ℓI< : Level} {I< : Rel I ℓI<} {ILO : isLinearOrder I<}
           {{ICO : CompatibleOrderStr ILO IPO}}
           {{I-Max : MaxOperationStr ILO}}
           {{LOA : LinearlyOrderedAdditiveStr ACM DLO}}
           {{POA : PartiallyOrderedAdditiveStr ACM DPO}}
           {{LOS : LinearlyOrderedSemiringStr S DLO}}
           {{SLOS : StronglyLinearlyOrderedSemiringStr S DLO}}
           {{POS : PartiallyOrderedSemiringStr S DPO}}
           {{DCO : CompatibleOrderStr DLO DPO}}
           where
   opaque
     trans-BigO : {f g h : I -> D} -> BigO f g -> BigO g h -> BigO f h
     trans-BigO {f} {g} {h} = ∥-map2 handle
       where
       handle : BigO' f g -> BigO' g h -> BigO' f h
       handle ((k1 , 0<k1) , n1 , b1) ((k2 , 0<k2) , n2 , b2) =
         (k1 * k2 , *-preserves-0< 0<k1 0<k2) , max n1 n2 , bound
         where
         bound : (i : I) -> (max n1 n2 ≤ i) -> abs (f i) ≤ ((k1 * k2) * h i)
         bound i ns≤i =
           trans-≤ (b1 i (trans-≤ max-≤-left ns≤i))
             (trans-≤-= (*₁-preserves-≤ (weaken-< 0<k1) (trans-≤ abs-≤ (b2 i (trans-≤ max-≤-right ns≤i))))
               (sym *-assoc))
