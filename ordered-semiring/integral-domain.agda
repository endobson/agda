{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.integral-domain where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import integral-domain
open import order
open import ordered-semiring
open import ring
open import semiring
open import truncation


module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM}
         {O : LinearOrderStr D ℓ<} {{LOS : LinearlyOrderedSemiringStr S O}}
         {AG : AdditiveGroup ACM}
         {R : Ring S AG}
         {A : TightApartnessStr D ℓD}
         {{ALO : ApartLinearOrderStr A O}}
         {{IntD : IntegralDomain R A}}  where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S
      IO = O
      IA = A

  StronglyLinearlyOrderedSemiringStr-IntegralDomain : StronglyLinearlyOrderedSemiringStr S O
  StronglyLinearlyOrderedSemiringStr-IntegralDomain = record
    { +₁-reflects-< = +₁-reflects-<'
    ; *₁-fully-reflects-< = *₁-fully-reflects-<'
    }
    where

    +₁-reflects-<' : {a b c : D} -> (a + b) < (a + c) -> (b < c)
    +₁-reflects-<' {a} ab<ac = subst2 _<_ p p (+₁-preserves-< ab<ac)
      where
      p : {x : D} -> (- a + (a + x)) == x
      p = sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero

    *₁-fully-reflects-<' : {a b c : D} -> (a * b) < (a * c) ->
        (b < c × 0# < a) ⊎ (c < b × a < 0#)
    *₁-fully-reflects-<' {a} {b} {c} ab<ac =
      handle (eqInv <>-equiv-# b#c) (eqInv <>-equiv-# a#0)
      where
      ab#ac : (a * b) # (a * c)
      ab#ac = eqFun <>-equiv-# (inj-l ab<ac)
      b#c : b # c
      b#c = *₁-reflects-# ab#ac
      a#0 : a # 0#
      a#0 = unsquash isProp-# (∥-map handle2 (comparison-# _ 0# _ ab#ac))
        where
        handle2 : ((a * b) # 0#) ⊎ (0# # (a * c)) -> a # 0#
        handle2 (inj-l ab#0) = *₂-reflects-#0 ab#0
        handle2 (inj-r 0#ac) = *₂-reflects-#0 (sym-# 0#ac)

      handle : ((b < c) ⊎ (c < b)) -> ((a < 0#) ⊎ (0# < a)) -> _
      handle (inj-l b<c) (inj-l a<0) =
        bot-elim (asym-< ab<ac (*₁-flips-< a<0 b<c))
      handle (inj-l b<c) (inj-r 0<a) = inj-l (b<c , 0<a)
      handle (inj-r c<b) (inj-l a<0) = inj-r (c<b , a<0)
      handle (inj-r c<b) (inj-r 0<a) =
        bot-elim (asym-< ab<ac (*₁-preserves-< 0<a c<b))
