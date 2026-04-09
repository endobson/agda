{-# OPTIONS --cubical --safe --exact-split #-}

module modular-integers.representative where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import equivalence
open import fin
open import int.base
open import isomorphism
open import modular-integers
open import nat
open import ring.implementations.int
open import semiring
open import set-quotient

open EqReasoning
open import quotient-remainder-int

module _ (n⁺ : Nat⁺) where
  private
    n = ⟨ n⁺ ⟩
    _~_ = ℤ/nℤ~ n

    repr : ℤ -> Fin n
    repr x = QuotientRemainder.r (quotient-remainder n⁺ x)

    opaque
      repr~ : (x y : ℤ) -> (x ~ y) -> repr x == repr y
      repr~ x y (d , p) = ans
        where
        qrx : QuotientRemainder n⁺ x
        qrx = quotient-remainder n⁺ x
        qry : QuotientRemainder n⁺ y
        qry = quotient-remainder n⁺ y
        module qrx = QuotientRemainder qrx
        module qry = QuotientRemainder qry
        ni : ℤ
        ni = int n

        check-p : d * ni == diff x y
        check-p = p

        x-path : qrx.q * ni + qrx.ri == x
        x-path = qrx.path

        y-path : qry.q * ni + qry.ri == y
        y-path = qry.path

        y-path2 : (d + qrx.q) * ni + qrx.ri == y
        y-path2 =
          begin
            (d + qrx.q) * ni + qrx.ri
          ==< +-left *-distrib-+-right >=> +-assoc >
            (d * ni) + ((qrx.q * ni) + qrx.ri)
          ==< cong2 _+_ p x-path >
            diff x y + x
          ==< +-commute >=> diff-step >
            y
          end

        qry2 : QuotientRemainder n⁺ y
        qry2 = record { q = d + qrx.q ; r = qrx.r ; path = y-path2 }

        ans : qrx.r == qry.r
        ans = cong QuotientRemainder.r (isProp-QuotientRemainder qry2 qry)


    ℤ/nℤ->representative : ℤ/nℤ n -> Fin n
    ℤ/nℤ->representative = SetQuotientElim.rec isSetFin repr repr~

    representative->ℤ/nℤ : Fin n -> ℤ/nℤ n
    representative->ℤ/nℤ (i , _) = [ (int i) ]

    opaque
      rep->ℤ/nℤ->rep : (i : Fin n) -> (ℤ/nℤ->representative (representative->ℤ/nℤ i)) == i
      rep->ℤ/nℤ->rep i = cong QuotientRemainder.r (isContr-QuotientRemainder .snd qr)
        where
        qr : QuotientRemainder n⁺ (int (Fin.i i))
        qr = record { q = (int 0) ; r = i ; path = +-left *-left-zero >=> +-left-zero }


      ℤ/nℤ->rep->ℤ/nℤ : (i : ℤ/nℤ n) -> (representative->ℤ/nℤ (ℤ/nℤ->representative i)) == i
      ℤ/nℤ->rep->ℤ/nℤ = SetQuotientElim.elimProp (\_ -> isSet-ℤ/nℤ _ _) handle
        where
        handle : (i : ℤ) -> (representative->ℤ/nℤ (ℤ/nℤ->representative [ i ])) == [ i ]
        handle i = eq/ _ _ r
          where
          module qr = QuotientRemainder (quotient-remainder n⁺ i)
          r : (int (Fin.i qr.r)) ~ i
          r = (qr.q ,
               sym +-right-zero >=> +-right (sym +-inverse) >=>
               sym +-assoc >=> +-left qr.path)

  ℤ/nℤ-Fin-eq : ℤ/nℤ n ≃ Fin n
  ℤ/nℤ-Fin-eq = isoToEquiv i
    where
    open Iso
    i : Iso (ℤ/nℤ n) (Fin n)
    i .fun = ℤ/nℤ->representative
    i .inv = representative->ℤ/nℤ
    i .rightInv = rep->ℤ/nℤ->rep
    i .leftInv = ℤ/nℤ->rep->ℤ/nℤ
