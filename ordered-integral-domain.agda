{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-integral-domain where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import integral-domain
open import order
open import ordered-ring
open import ordered-semiring
open import ring
open import semiring

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {O : LinearOrderStr D ℓ<}
         {R : Ring S AG} {A : TightApartnessStr D}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{ALO : ApartLinearOrderStr A O}}
         {{ID : IntegralDomain R A}}
         where
  private
    instance
      IS = S
      IR = R
      IO = O
      IACM = ACM
      IA = A

  abstract
    *₁-reflects-< : {a b c : D} -> (0# < a) -> (a * b) < (a * c) -> (b < c)
    *₁-reflects-< {a} {b} {c} 0<a ab<ac = handle (eqInv (<>-equiv-# _ _) b#c)
      where
      ab#ac : (a * b) # (a * c)
      ab#ac = eqFun (<>-equiv-# _ _) (inj-l ab<ac)
      b#c : b # c
      b#c = *₁-reflects-# ab#ac
      handle : (b < c) ⊎ (c < b) -> b < c
      handle (inj-l b<c) = b<c
      handle (inj-r c<b) = bot-elim (asym-< ab<ac (*₁-preserves-< 0<a c<b))

    *₂-reflects-< : {a b c : D} -> (a * c) < (b * c) -> (0# < c) -> (a < b)
    *₂-reflects-< {a} {b} {c} ac<bc 0<c =
      *₁-reflects-< 0<c (subst2 _<_ *-commute *-commute ac<bc)
