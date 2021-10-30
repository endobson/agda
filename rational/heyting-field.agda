{-# OPTIONS --cubical --safe --exact-split #-}

module rational.heyting-field where

open import additive-group
open import apartness
open import base
open import cubical
open import equality
open import functions
open import isomorphism
open import heyting-field
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.difference
open import rational.order
open import relation
open import semiring
open import sign
open import sign.instances.rational
open import sum
open import truncation
open import univalence

private
  open RationalRing using (isUnit ; is-unit ; isProp-isUnit)

  ℚInv-equiv-isUnit : (q : ℚ) -> ℚInv q ≃ isUnit q
  ℚInv-equiv-isUnit q = isoToEquiv i
    where
    open Iso
    i : Iso (ℚInv q) (isUnit q)
    i .fun inv = is-unit (r1/ q inv) (*-commute >=> r1/-inverse q inv)
    i .inv (is-unit 1/q path) q=0 =
      1r!=0r (sym path >=> *-left q=0 >=> *-left-zero)
    i .rightInv _ = isProp-isUnit _ _
    i .leftInv _ = isProp¬ _ _ _

  ℚ<> : Rel ℚ ℓ-zero
  ℚ<> q r = (q < r) ⊎ (r < q)

  isProp-ℚ<> : (q r : ℚ) -> isProp (ℚ<> q r)
  isProp-ℚ<> q r = isProp⊎ (isProp-< q r) (isProp-< r q) asym-<

  irrefl-ℚ<> : Irreflexive ℚ<>
  irrefl-ℚ<> (inj-l r<r) = irrefl-< r<r
  irrefl-ℚ<> (inj-r r<r) = irrefl-< r<r

  sym-ℚ<> : Symmetric ℚ<>
  sym-ℚ<> = ⊎-swap

  comparison-ℚ<> : Comparison ℚ<>
  comparison-ℚ<> a b c (inj-l a<c) =
    ∥-map (⊎-map inj-l inj-l) (comparison-< a b c a<c)
  comparison-ℚ<> a b c (inj-r c<a) =
    ∥-map (⊎-swap ∘ ⊎-map inj-r inj-r) (comparison-< c b a c<a)

  tight-ℚ<> : Tight ℚ<>
  tight-ℚ<> {q} {r} ¬q<>r = handle (trichotomous-< q r)
    where
    handle : Tri (q < r) (q == r) (r < q) -> (q == r)
    handle (tri< q<r _ _) = bot-elim (¬q<>r (inj-l q<r))
    handle (tri= _ q=r _) = q=r
    handle (tri> _ _ r<q) = bot-elim (¬q<>r (inj-r r<q))

  tight-apartness-ℚ<> : TightApartness ℚ<>
  tight-apartness-ℚ<> = (tight-ℚ<> , irrefl-ℚ<> , sym-ℚ<> , comparison-ℚ<>)


  ℚ<>-equiv-ℚInv : (q r : ℚ) -> ℚ<> q r ≃ ℚInv (diffℚ q r)
  ℚ<>-equiv-ℚInv q r = isoToEquiv i
    where
    open Iso
    i : Iso (ℚ<> q r) (ℚInv (diffℚ q r))
    i .fun (inj-l q<r) d=0 = NonZero->¬Zero (subst NonZero d=0 (inj-l (Pos-diffℚ q r q<r))) Zero-0r
    i .fun (inj-r r<q) d=0 =
      NonZero->¬Zero (subst NonZero (sym (diffℚ-anticommute _ _) >=> d=0)
                            (inj-r (r--flips-sign _ pos-sign (Pos-diffℚ r q r<q)))) Zero-0r
    i .inv d!=0 = handle (trichotomous-< q r)
      where
      handle : Tri (q < r) (q == r) (r < q) -> ℚ<> q r
      handle (tri< q<r _ _) = inj-l q<r
      handle (tri= _ q=r _) = bot-elim (d!=0 (+-right (cong -_ q=r) >=> +-inverse))
      handle (tri> _ _ r<q) = inj-r r<q
    i .rightInv _ = isProp¬ _ _ _
    i .leftInv _ = isProp-ℚ<> _ _ _ _

  ℚ<>=isUnitℚ : (q r : ℚ) -> (ℚ<> q r) == isUnit (diffℚ q r)
  ℚ<>=isUnitℚ q r = (ua (ℚ<>-equiv-ℚInv q r)) >=> (ua (ℚInv-equiv-isUnit (diffℚ q r)))

  abstract
    TightApartness-ℚ# : TightApartness (\q r -> (isUnit (diffℚ q r)))
    TightApartness-ℚ# =
      subst TightApartness (\i q r -> ℚ<>=isUnitℚ q r i) tight-apartness-ℚ<>

instance
  TightApartnessStr-ℚ : TightApartnessStr ℚ
  TightApartnessStr-ℚ = record
    { _#_ = \q r -> isUnit (diffℚ q r)
    ; TightApartness-# = TightApartness-ℚ#
    ; isProp-# = \x y -> RationalRing.isProp-isUnit
    }

  RationalField : Field RationalRing TightApartnessStr-ℚ
  RationalField = record
    { f#-path = refl
    }
