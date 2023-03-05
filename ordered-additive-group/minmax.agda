{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.minmax where

open import additive-group
open import base
open import equality
open import order
open import order.minmax
open import ordered-additive-group
open import truncation
open import hlevel.base

module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {LO : LinearOrderStr D ℓ<}
         {{Min : MinOperationStr LO}}
         {{Max : MaxOperationStr LO}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
  where
  private
    instance
      IACM = ACM
      ILO = LO

  min+max=sum : {a b : D} -> (min a b) + (max a b) == a + b
  min+max=sum {a} {b} = connected-< case1 case2
    where
    case1 : (min a b + max a b) ≮ (a + b)
    case1 min+max<ab = unsquash isPropBot (∥-map handle (+-reflects-< min+max<ab))
      where
      handle : (min a b < a) ⊎ (max a b < b) -> Bot
      handle (inj-r max<b) = max-≮-right max<b
      handle (inj-l min<a) =
        irrefl-path-< (cong2 _+_ min=b max=a >=> +-commute) min+max<ab
        where
        min=b : min a b == b
        min=b = min-<-left-path min<a

        b<a : b < a
        b<a = trans-=-< (sym min=b) min<a

        max=a : max a b == a
        max=a = max-commute >=> max-<-path b<a

    case2 : (min a b + max a b) ≯ (a + b)
    case2 min+max>ab = unsquash isPropBot (∥-map handle (+-reflects-< min+max>ab))
      where
      handle : (a < min a b) ⊎ (b < max a b) -> Bot
      handle (inj-l a<min) = min-≮-left a<min
      handle (inj-r b<max) =
        irrefl-path-< (sym (cong2 _+_ min=b max=a >=> +-commute)) min+max>ab
        where
        max=a : max a b == a
        max=a = max-<-right-path b<max

        b<a : b < a
        b<a = trans-<-= b<max max=a

        min=b : min a b == b
        min=b = min-commute >=> min-<-path b<a
