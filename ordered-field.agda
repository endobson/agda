{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-field where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import heyting-field
open import order
open import ordered-semiring
open import ordered-ring
open import ring
open import semiring
open import sum

private
  variable
    ℓD ℓ< : Level

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {R : Ring S AG} {A : TightApartnessStr D}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{F : Field R A}}
         {{AL : ApartLinearOrderStr A O}}
         where
  private
    module F = Field F
    module R = Ring R
    instance
      ILOS = LOS
      IACM = ACM
      IS = S
      IO = O
      IR = R
      IA = A
      IAL = AL

  private
    2# : D
    2# = 1# + 1#

    0<1# : 0# < 1#
    0<1# = proj-¬l (eqInv (<>-equiv-# 1# 0#) F.1#0) 1≮0#

    0<2# : 0# < 2#
    0<2# = +-preserves-0< 0<1# 0<1#

    2#0 : 2# # 0#
    2#0 = (eqFun (<>-equiv-# 2# 0#) (inj-r 0<2#))

    1/2u = R.u1/ (2# , F.#0->isUnit 2#0) -- (F.#0->isUnit 2#0)) -- (R.is-unit 2# )
    1/2# = fst 1/2u

    2#-path : (x : D) -> x + x == 2# * x
    2#-path x = +-cong (sym *-left-one) (sym *-left-one) >=>
                sym *-distrib-+-right

    2#-1/2#-path : 2# * 1/2# == 1#
    2#-1/2#-path = *-commute >=> R.isUnit.path (snd 1/2u)

    1/2#-+-path : 1/2# + 1/2# == 1#
    1/2#-+-path = 2#-path 1/2# >=> 2#-1/2#-path

    1/2#-path : {x : D} -> (1/2# * x) + (1/2# * x) == x
    1/2#-path = sym *-distrib-+-right >=> *-left 1/2#-+-path >=> *-left-one


  -- +-reflects-0< : (x y : D) -> 0# < (x + y) -> ∥ 0# < x ⊎ 0# < y ∥
  -- +-reflects-0< x y = ?
