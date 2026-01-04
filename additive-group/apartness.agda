{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.apartness where

open import additive-group
open import apartness
open import base
open import equality-path
open import functions
open import relation
open import sum
open import truncation


module _ {ℓ ℓ# : Level} {D : Type ℓ} {D# : Rel D ℓ#} (ACM : AdditiveCommMonoid D)
         (A : isTightApartness D#) where
  private
    instance
      IACM = ACM
      IA = A

  record ApartAdditiveCommMonoid : Type (ℓ-max ℓ ℓ#) where
    no-eta-equality
    field
      StronglyInjective-+₁ : ∀ (a : D) -> StronglyInjective (a +_)
      StronglyExtensional-+₁ : ∀ (a : D) -> StronglyExtensional (a +_)


module _ {ℓ ℓ# : Level} {D : Type ℓ} {D# : Rel D ℓ#} {{ACM : AdditiveCommMonoid D}}
         {{A : isTightApartness D#}} {{AACM : ApartAdditiveCommMonoid ACM A}}
  where
  private
    module AACM = ApartAdditiveCommMonoid AACM


  opaque
    +₁-preserves-# : {a b c : D} -> (b # c) -> (a + b) # (a + c)
    +₁-preserves-# = AACM.StronglyInjective-+₁ _

    +₂-preserves-# : {a b c : D} -> (a # b) -> (a + c) # (b + c)
    +₂-preserves-# a#b = subst2 _#_ +-commute +-commute (+₁-preserves-# a#b)

    +₁-reflects-# : {a b c : D} -> (a + b) # (a + c) -> (b # c)
    +₁-reflects-# = AACM.StronglyExtensional-+₁ _

    +₂-reflects-# : {a b c : D} -> (a + c) # (b + c) -> (a # b)
    +₂-reflects-# ac#bc = +₁-reflects-# (subst2 _#_ +-commute +-commute ac#bc)

    +-reflects-# : {d1 d2 d3 d4 : D} -> (d1 + d2) # (d3 + d4) -> ∥ (d1 # d3) ⊎ (d2 # d4) ∥
    +-reflects-# {d1} {d2} {d3} {d4} =
      ∥-map (⊎-map +₂-reflects-# +₁-reflects-#) ∘ (comparison-# _ _ _)

    +-reflects-#0 : {a b : D} -> (a + b) # 0# -> ∥ (a # 0#) ⊎ (b # 0#) ∥
    +-reflects-#0 {a} {b} ab#0 = +-reflects-# (subst ((a + b) #_) (sym +-right-zero) ab#0)


module _ {ℓ ℓ# : Level} {D : Type ℓ} {D# : Rel D ℓ#} {{ACM : AdditiveCommMonoid D}}
         {{A : isTightApartness D#}} {{AACM : ApartAdditiveCommMonoid ACM A}}
         {{AG : AdditiveGroup ACM}} where

  opaque
    minus-preserves-# : {a b : D} -> a # b -> (- a) # (- b)
    minus-preserves-# a#b =
      subst2 _#_ (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
                 (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
                 (+₁-preserves-# (sym-# a#b))

    minus-preserves-#0 : {a : D} -> a # 0# -> (- a) # 0#
    minus-preserves-#0 {a} a#0 = subst ((- a) #_) minus-zero (minus-preserves-# a#0)

    #->diff#0 : {a b : D} -> a # b -> diff a b # 0#
    #->diff#0 {a} {b} a#b =
      subst (diff a b #_) +-inverse (+₂-preserves-# (sym-# a#b))

    diff#0-># : {a b : D} -> diff a b # 0# -> a # b
    diff#0-># {a} {b} d#0 = sym-# (subst2 _#_ diff-step +-right-zero (+₁-preserves-# d#0))
