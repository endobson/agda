{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.squares where

open import additive-group
open import equality
open import ordered-semiring
open import ordered-semiring.negated
open import equivalence
open import semiring
open import ring
open import order
open import base
open import truncation
open import functions

module _ {ℓD ℓ< : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}} where
  private
    instance
      IACM = ACM
      ILO = LO
      IS = S
      PO = NegatedLinearOrder LO
      CPO = CompatibleNegatedLinearOrder LO
      POS = PartiallyOrderedSemiringStr-Negated S LO

  squares-ordered⁺ : {q r : D} -> (q ≮ 0#) -> (q < r) -> (q * q) < (r * r)
  squares-ordered⁺ {q} {r} q≮0 q<r =
    trans-≤-< (*₁-preserves-≤ (convert-≮ q≮0) (weaken-< q<r)) (*₂-preserves-< q<r 0<r)
    where
    module _ where
      0<r = trans-≤-< (convert-≮ q≮0) q<r

  squares-ordered-< : {q r : D} -> (r ≮ 0#) -> (q * q) < (r * r) -> q < r
  squares-ordered-< {q} {r} r≮0 qq<rr =
    unsquash isProp-< (∥-map handle (comparison-< qq qr rr qq<rr))
    where
    module _ where
      qq = (q * q)
      qr = (q * r)
      rr = (r * r)

      r≮q : r ≮ q
      r≮q r<q = asym-< qq<rr (squares-ordered⁺ r≮0 r<q)

      handle : (qq < qr) ⊎ (qr < rr) -> q < r
      handle (inj-r qr<rr) = *₂-reflects-< qr<rr r≮0
      handle (inj-l qq<qr) = handle2 (*₁-fully-reflects-< qq<qr)
        where
        handle2 : (q < r × 0# < q) ⊎ (r < q × q < 0#) -> q < r
        handle2 (inj-l (q<r , _)) = q<r
        handle2 (inj-r (r<q , _)) = bot-elim (r≮q r<q)

  square-≮0 : {x : D} -> (x * x) ≮ 0#
  square-≮0 {x} xx<0 = handle (*₁-fully-reflects-< (trans-<-= xx<0 (sym *-right-zero)))
    where
    handle : (x < 0# × 0# < x) ⊎ (0# < x × x < 0#) -> Bot
    handle (inj-l (x<0 , 0<x)) = asym-< x<0 0<x
    handle (inj-r (0<x , x<0)) = asym-< x<0 0<x

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : LinearOrderStr D ℓ<} {PO : PartialOrderStr D ℓ≤}
         {{COS : CompatibleOrderStr LO PO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}} where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = PO
      IS = S

  squares-ordered-≤ : {q r : D} -> (0# ≤ r) -> (q * q) ≤ (r * r) -> q ≤ r
  squares-ordered-≤ {q} {r} 0≤r qq≤rr =
    convert-≮ (\r<q -> irrefl-< (trans-<-≤ (squares-ordered⁺ (convert-≤ 0≤r) r<q) qq≤rr))
