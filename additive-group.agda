{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group where

open import apartness
open import base
open import commutative-monoid
open import equality
open import group
open import hlevel
open import monoid
open import relation
open import truncation

record AdditiveCommMonoid {ℓ : Level} (D : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    comm-monoid : CommMonoid D

  isSet-Domain : isSet D
  isSet-Domain = CommMonoid.isSet-Domain comm-monoid

module _ {ℓ : Level} (D : Type ℓ) {{ACM : AdditiveCommMonoid D}} where
  CommMonoid-+ : CommMonoid D
  CommMonoid-+ = AdditiveCommMonoid.comm-monoid ACM

  Monoid-+ : Monoid D
  Monoid-+ = CommMonoid.monoid CommMonoid-+

module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}} where
  private
    module CM = CommMonoid (CommMonoid-+ D)
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

    +-left-zeroᵉ : (m : D) -> (0# + m) == m
    +-left-zeroᵉ _ = CM.∙-left-ε

    +-right-zero : {m : D} -> (m + 0#) == m
    +-right-zero = CM.∙-right-ε

    +-right-zeroᵉ : (m : D) -> (m + 0#) == m
    +-right-zeroᵉ _ = CM.∙-right-ε

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


module _ {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
         {{ACM₁ : AdditiveCommMonoid D₁}}
         {{ACM₂ : AdditiveCommMonoid D₂}} where
  AdditiveCommMonoidʰ : (D₁ -> D₂) -> Type (ℓ-max ℓ₁ ℓ₂)
  AdditiveCommMonoidʰ f =
    CommMonoidʰᵉ (AdditiveCommMonoid.comm-monoid ACM₁)
                 (AdditiveCommMonoid.comm-monoid ACM₂)
                 f


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
    group-str .GroupStr.monoid = CommMonoid.monoid (AdditiveCommMonoid.comm-monoid ACM)
    group-str .GroupStr.inverse = -_
    group-str .GroupStr.∙-left-inverse = +-commute >=> +-inverse
    group-str .GroupStr.∙-right-inverse = +-inverse

    ab-group-str : AbGroupStr D
    ab-group-str .AbGroupStr.comm-monoid = AdditiveCommMonoid.comm-monoid ACM
    ab-group-str .AbGroupStr.inverse = -_
    ab-group-str .AbGroupStr.∙-left-inverse = +-commute >=> +-inverse
    ab-group-str .AbGroupStr.∙-right-inverse = +-inverse


module _ {ℓ : Level} (D : Type ℓ) {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}} where
  GroupStr-+ : GroupStr D
  GroupStr-+ = AdditiveGroup.group-str AG


module _ {ℓ : Level} {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{AG : AdditiveGroup ACM}} where
  open AdditiveGroup AG public using (-_)
  open EqReasoning

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

    diff0-path : {x : D} -> diff 0# x == x
    diff0-path = sym +-left-zero >=> diff-step

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

    +₁-preserves-diff : {a b c : D} -> diff a b == diff (c + a) (c + b)
    +₁-preserves-diff =
      sym +-left-zero >=> +-left (sym +-inverse) >=> +-swap-diff

    +₂-preserves-diff : {a b c : D} -> diff a b == diff (a + c) (b + c)
    +₂-preserves-diff =
      +₁-preserves-diff >=> cong2 diff +-commute +-commute


module _ {ℓ ℓ# : Level} {D : Type ℓ} {D# : Rel D ℓ#} {ACM : AdditiveCommMonoid D}
         (AG : AdditiveGroup ACM) (A : isTightApartness D#) where
  private
    instance
      IACM = ACM
      IAG = AG
      IA = A

  record ApartAdditiveGroup : Type (ℓ-max ℓ ℓ#) where
    no-eta-equality
    field
      +-reflects-# : {d1 d2 d3 d4 : D} -> (d1 + d2) # (d3 + d4) -> ∥ (d1 # d3) ⊎ (d2 # d4) ∥

module _ {ℓ ℓ# : Level} {D : Type ℓ} {D# : Rel D ℓ#} {ACM : AdditiveCommMonoid D}
         {AG : AdditiveGroup ACM} {A : isTightApartness D#}
         {{AAG : ApartAdditiveGroup AG A}} where
  private
    instance
      IACM = ACM
      IAG = AG
      IA = A

  abstract
    +-reflects-# : {d1 d2 d3 d4 : D} -> (d1 + d2) # (d3 + d4) -> ∥ (d1 # d3) ⊎ (d2 # d4) ∥
    +-reflects-# = ApartAdditiveGroup.+-reflects-# AAG

    +₁-preserves-# : {a b c : D} -> (b # c) -> (a + b) # (a + c)
    +₁-preserves-# {a} {b} {c} b#c =
      unsquash isProp-# (∥-map handle (+-reflects-# ap))
      where
      module _ where
        handle : ((a + b) # (a + c)) ⊎ ((- a) # (- a)) -> ((a + b) # (a + c))
        handle (inj-l ap2) = ap2
        handle (inj-r ap2) = bot-elim (irrefl-# ap2)

        ap : ((a + b) + (- a)) # ((a + c) + (- a))
        ap = subst2 _#_ (sym +-right-zero >=> +-right (sym +-inverse) >=> sym +-assoc >=> +-left +-commute)
                        (sym +-right-zero >=> +-right (sym +-inverse) >=> sym +-assoc >=> +-left +-commute)
                        b#c

    +₂-preserves-# : {a b c : D} -> (a # b) -> (a + c) # (b + c)
    +₂-preserves-# a#b = subst2 _#_ +-commute +-commute (+₁-preserves-# a#b)


    +-reflects-#0 : {a b : D} -> (a + b) # 0# -> ∥ (a # 0#) ⊎ (b # 0#) ∥
    +-reflects-#0 {a} {b} ab#0 = +-reflects-# (subst ((a + b) #_) (sym +-right-zero) ab#0)

    minus-preserves-# : {a b : D} -> a # b -> (- a) # (- b)
    minus-preserves-# a#b =
      subst2 _#_ (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
                 (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
                 (+₁-preserves-# (sym-# a#b))

    minus-preserves-#0 : {a : D} -> a # 0# -> (- a) # 0#
    minus-preserves-#0 {a} a#0 = subst ((- a) #_) minus-zero (minus-preserves-# a#0)
