{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.minmax where

open import additive-group
open import base
open import equality
open import hlevel.base
open import order
open import order.minmax
open import ordered-additive-group
open import ordered-additive-group.negated
open import relation
open import truncation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {ACM : AdditiveCommMonoid D}
         {LO : isLinearOrder D<}
         {{Min : MinOperationStr LO}}
         {{Max : MaxOperationStr LO}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
  where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = isLinearOrder->isPartialOrder-≯ LO
      CPO = CompatibleNegatedLinearOrder LO
      POA = PartiallyOrderedAdditiveStr-Negated ACM LO

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

  module _ {{AG : AdditiveGroup ACM}} where
    minus-max-path : {a b : D} -> - (max a b) == min (- a) (- b)
    minus-max-path {a} {b} = antisym-≤ case1 case2
      where
      case1 : (- max a b) ≤ min (- a) (- b)
      case1 = min-greatest-≤ max≤-a max≤-b
        where
        max≤-a : (- max a b) ≤ (- a)
        max≤-a = minus-flips-≤ max-≤-left
        max≤-b : (- max a b) ≤ (- b)
        max≤-b = minus-flips-≤ max-≤-right

      case2 : min (- a) (- b) ≤ (- max a b)
      case2 = trans-=-≤ (sym minus-double-inverse) (minus-flips-≤ max≤-min)
        where
        min≤-a : min (- a) (- b) ≤ (- a)
        min≤-a = min-≤-left
        min≤-b : min (- a) (- b) ≤ (- b)
        min≤-b = min-≤-right
        a≤-min : a ≤ (- (min (- a) (- b)))
        a≤-min = trans-=-≤ (sym minus-double-inverse) (minus-flips-≤ min≤-a)
        b≤-min : b ≤ (- (min (- a) (- b)))
        b≤-min = trans-=-≤ (sym minus-double-inverse) (minus-flips-≤ min≤-b)
        max≤-min : max a b ≤ (- (min (- a) (- b)))
        max≤-min = max-least-≤ a≤-min b≤-min

    minus-min-path : {a b : D} -> - (min a b) == max (- a) (- b)
    minus-min-path {a} {b} = antisym-≤ case1 case2
      where
      case1 : (- min a b) ≤ max (- a) (- b)
      case1 = trans-≤-= (minus-flips-≤ min≤-max) minus-double-inverse
        where
        -a≤max : (- a) ≤ max (- a) (- b)
        -a≤max = max-≤-left
        -b≤max : (- b) ≤ max (- a) (- b)
        -b≤max = max-≤-right
        max≤a : (- (max (- a) (- b))) ≤ a
        max≤a = trans-≤-= (minus-flips-≤ -a≤max) minus-double-inverse
        max≤b : (- (max (- a) (- b))) ≤ b
        max≤b = trans-≤-= (minus-flips-≤ -b≤max) minus-double-inverse
        min≤-max : (- (max (- a) (- b))) ≤ min a b
        min≤-max = min-greatest-≤ max≤a max≤b

      case2 : max (- a) (- b) ≤ (- min a b)
      case2 = max-least-≤ -a≤min -b≤min
        where
        -a≤min : (- a) ≤ (- min a b)
        -a≤min = minus-flips-≤ min-≤-left
        -b≤min : (- b) ≤ (- min a b)
        -b≤min = minus-flips-≤ min-≤-right


module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤} {ACM : AdditiveCommMonoid D}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{Min : MinOperationStr LO}}
         {{Max : MaxOperationStr LO}}
         {{COS : CompatibleOrderStr LO PO}}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
  where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = PO

  min-+-swap : {a b c d : D} -> (min a b + min c d) ≤ min (a + c) (b + d)
  min-+-swap = min-greatest-≤ abcd≤ac abcd≤bd
    where
    abcd≤ac = +-preserves-≤ min-≤-left min-≤-left
    abcd≤bd = +-preserves-≤ min-≤-right min-≤-right

  max-+-swap : {a b c d : D} -> max (a + c) (b + d) ≤ (max a b + max c d)
  max-+-swap = max-least-≤ abcd≤ac abcd≤bd
    where
    abcd≤ac = +-preserves-≤ max-≤-left max-≤-left
    abcd≤bd = +-preserves-≤ max-≤-right max-≤-right
