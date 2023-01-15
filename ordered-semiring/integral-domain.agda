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


module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}  {S : Semiring ACM}
         {O : LinearOrderStr D ℓ<} {{LOS : LinearlyOrderedSemiringStr S O}}
         {AG : AdditiveGroup ACM}
         {R : Ring S AG}
         {A : TightApartnessStr D}
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
    ; *₁-reflects-< = *₁-reflects-<'
    }
    where

    +₁-reflects-<' : {a b c : D} -> (a + b) < (a + c) -> (b < c)
    +₁-reflects-<' {a} ab<ac = subst2 _<_ p p (+₁-preserves-< ab<ac)
      where
      p : {x : D} -> (- a + (a + x)) == x
      p = sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero

    *₁-reflects-<' : {a b c : D} -> (0# < a) -> (a * b) < (a * c) -> (b < c)
    *₁-reflects-<' {a} {b} {c} 0<a ab<ac = handle (eqInv <>-equiv-# b#c)
      where
      module _ where
        ab#ac : (a * b) # (a * c)
        ab#ac = eqFun <>-equiv-# (inj-l ab<ac)
        b#c : b # c
        b#c = *₁-reflects-# ab#ac
        handle : (b < c) ⊎ (c < b) -> b < c
        handle (inj-l b<c) = b<c
        handle (inj-r c<b) = bot-elim (asym-< ab<ac (*₁-preserves-< 0<a c<b))
