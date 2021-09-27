{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group where

open import base
open import equality
open import commutative-monoid
open import group
open import hlevel

record AdditiveCommMonoid {ℓ : Level} (D : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    comm-monoid : CommMonoid D

  isSet-Domain : isSet D
  isSet-Domain = CommMonoid.isSet-Domain comm-monoid

module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} where
  private
    module CM = CommMonoid (AdditiveCommMonoid.comm-monoid ACM)
  infixl 6 _+_

  _+_ : D -> D -> D
  _+_ = CM._∙_

  0# : D
  0# = CM.ε

  abstract
    +-assoc : {m n o : D} -> (m + n) + o == m + (n + o)
    +-assoc = CM.∙-assoc

    +-assocᵉ : (m n o : D) -> (m + n) + o == m + (n + o)
    +-assocᵉ _ _ _ = CM.∙-assoc

    +-left-zero : {m : D} -> (0# + m) == m
    +-left-zero = CM.∙-left-ε

    +-right-zero : {m : D} -> (m + 0#) == m
    +-right-zero = CM.∙-right-ε

    +-commute : {m n : D} -> (m + n) == (n + m)
    +-commute = CM.∙-commute

    +-commuteᵉ : (m n : D) -> (m + n) == (n + m)
    +-commuteᵉ _ _ = CM.∙-commute

  abstract
    +-right : {m n p : D} -> (n == p) -> m + n == m + p
    +-right {m} id = cong (\x -> m + x) id

    +-left : {m n p : D} -> (n == p) -> n + m == p + m
    +-left {m} id = cong (\x -> x + m) id

    +-cong : {m n p o : D} -> m == p -> n == o -> m + n == p + o
    +-cong = cong2 _+_

    +-swap : {m n o p : D} -> (m + n) + (o + p) == (m + o) + (n + p)
    +-swap = +-assoc >=> +-right (sym +-assoc >=> +-left +-commute >=> +-assoc) >=> sym +-assoc


module _ {ℓ : Level} {D : Type ℓ} (ACM : AdditiveCommMonoid D) where
  private
    instance
      IACM = ACM

  record AdditiveGroup  : Type ℓ where
    no-eta-equality
    field
      -_ : D -> D
      +-inverse : {x : D} -> x + (- x) == 0#

    group-str : GroupStr D
    group-str .GroupStr.comm-monoid = AdditiveCommMonoid.comm-monoid ACM
    group-str .GroupStr.inverse = -_
    group-str .GroupStr.∙-left-inverse = +-commute >=> +-inverse

module _ {ℓ : Level} {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}} where
  open AdditiveGroup AG public using (-_)
  private
    module AG = AdditiveGroup AG

    instance
      IACM = ACM

  abstract
    +-inverse : {x : D} -> x + (- x) == 0#
    +-inverse = AG.+-inverse

    +-inverseᵉ : (x : D) -> x + (- x) == 0#
    +-inverseᵉ _ = AG.+-inverse

  abstract
    minus-zero : Path D (- 0#) 0#
    minus-zero =
      begin
        (- 0#)
      ==< sym +-left-zero >
        0# + (- 0#)
      ==< +-inverse >
        0#
      end

    minus-unique : {a b : D} -> a + b == 0# -> b == - a
    minus-unique {a} {b} pr =
      begin
        b
      ==< sym +-left-zero >
        0# + b
      ==< +-left (sym +-inverse) >
        (a + - a) + b
      ==< +-left +-commute >
        (- a + a) + b
      ==< +-assoc >
        - a + (a + b)
      ==< +-right pr >
        - a + 0#
      ==< +-right-zero  >
        - a
      end

    minus-double-inverse : {a : D} -> - - a == a
    minus-double-inverse {a} = sym (minus-unique
      (begin
         - a + a
       ==< +-commute >
         a + - a
       ==< +-inverse >
         0#
       end))

    minus-distrib-plus : {a b : D} -> - (a + b) == - a + - b
    minus-distrib-plus {a} {b} = sym (minus-unique p)
      where
      p : (a + b) + (- a + - b) == 0#
      p = +-swap >=> +-cong +-inverse +-inverse >=> +-right-zero

    minus-distrib-plusᵉ : (a b : D) -> - (a + b) == - a + - b
    minus-distrib-plusᵉ _ _ = minus-distrib-plus

  diff : D -> D -> D
  diff d1 d2 = d2 + (- d1)


  abstract
    diff-anticommute : {a b : D} -> diff a b == - (diff b a)
    diff-anticommute = sym (
      minus-distrib-plus >=>
      +-right minus-double-inverse >=>
      +-commute)

    diff-anticommuteᵉ : (a b : D) -> diff a b == - (diff b a)
    diff-anticommuteᵉ _ _ = diff-anticommute

    diff-trans : {x y z : D} -> diff x y + diff y z == diff x z
    diff-trans {x} {y} {z} =
      +-commute >=>
      +-assoc >=>
      +-right (sym +-assoc >=>
               +-left (+-commute >=> +-inverse) >=>
               +-left-zero)

    diff-transᵉ : (x y z : D) -> diff x y + diff y z == diff x z
    diff-transᵉ _ _ _ = diff-trans

    diff-step : {x y : D} -> x + diff x y == y
    diff-step =
      sym +-assoc >=>
      +-left +-commute >=>
      +-assoc >=>
      +-right +-inverse >=>
      +-right-zero

    diff-zero : {x y : D} -> diff x y == 0# -> x == y
    diff-zero p = sym +-right-zero >=> +-right (sym p) >=> diff-step

    +-swap-diff : {a b c d : D} -> ((diff a b) + (diff c d)) == (diff (a + c) (b + d))
    +-swap-diff {a} {b} {c} {d} =
      +-assoc >=>
      +-right (sym +-assoc >=>
               +-left +-commute >=>
               +-assoc >=>
               +-right (sym (minus-distrib-plus))) >=>
      sym +-assoc

    +-swap-diffᵉ : (a b c d : D) -> ((diff a b) + (diff c d)) == (diff (a + c) (b + d))
    +-swap-diffᵉ _ _ _ _ = +-swap-diff
