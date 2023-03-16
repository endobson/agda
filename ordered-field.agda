{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-field where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import heyting-field
open import hlevel
open import integral-domain.instances.heyting-field
open import nat
open import order
open import ordered-additive-group
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.integral-domain
open import ring
open import semiring
open import sigma.base
open import sum
open import truncation

private
  variable
    ℓD ℓ< : Level

module _ {D : Type ℓD} {ACM : AdditiveCommMonoid D} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {O : LinearOrderStr D ℓ<}
         {R : Ring S AG} {A : TightApartnessStr D ℓD}
         {{LOA : LinearlyOrderedAdditiveStr ACM O}}
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
      IAG = AG
      IS = S
      IO = O
      IR = R
      IA = A
      IAL = AL
      IID = IntegralDomain-Field
      ISOS = StronglyLinearlyOrderedSemiringStr-IntegralDomain

    isSet-D : isSet D
    isSet-D = Semiring.isSet-Domain S

  private
    2# : D
    2# = 1# + 1#

    0<1# : 0# < 1#
    0<1# = proj-¬l (eqInv <>-equiv-# F.1#0) 1≮0

    0<2# : 0# < 2#
    0<2# = +-preserves-0< 0<1# 0<1#

    2#0 : 2# # 0#
    2#0 = (eqFun <>-equiv-# (inj-r 0<2#))

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

    iℕ : Nat -> D
    iℕ zero = 0#
    iℕ (suc n) = 1# + iℕ n

    0<iℕ : (n : Nat⁺) -> 0# < iℕ ⟨ n ⟩
    0<iℕ (suc zero , _) = trans-<-= 0<1# (sym +-right-zero)
    0<iℕ (suc (suc n) , _) =
      +-preserves-0< 0<1# (0<iℕ (suc n , tt))

  ∃!1/ℕ : (n : Nat⁺) -> ∃![ d ∈ D ] (iℕ ⟨ n ⟩ * d == 1#)
  ∃!1/ℕ n = (R.isUnit.inv u , R.isUnit.path u) , p _
    where
    u = (F.#0->isUnit (eqFun <>-equiv-# (inj-r (0<iℕ n))))
    p : isProp (Σ[ d ∈ D ] (iℕ ⟨ n ⟩ * d == 1#))
    p (d1 , p1) (d2 , p2) = ΣProp-path (isSet-D _ _) p3
      where
      p3 : d1 == d2
      p3 = sym (*-left-one) >=>
           (cong (_* d1) (sym p2 >=> *-commute)) >=>
           *-assoc >=> *-commute >=>
           (cong (_* d2) p1) >=> *-left-one


  1/ℕ : (n : Nat⁺) -> D
  1/ℕ n = ∃!-val (∃!1/ℕ n)

  0<1/ℕ : (n : Nat⁺) -> 0# < 1/ℕ n
  0<1/ℕ n = *₁-reflects-0< (asym-< (0<iℕ n)) (trans-<-= 0<1# (sym (∃!-prop (∃!1/ℕ n))))
