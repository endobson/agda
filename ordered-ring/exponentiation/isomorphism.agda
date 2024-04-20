{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.exponentiation.isomorphism where

open import additive-group
open import base
open import equality-path
open import finsum
open import finsum.arithmetic
open import funext
open import isomorphism
open import nat
open import nat.even-odd
open import order
open import ordered-additive-group
open import ordered-ring.exponentiation.poly-index
open import ordered-ring.exponentiation.poly-index.eval
open import ordered-ring.exponentiation.poly-index.ends
open import ordered-semiring
open import relation
open import ring
open import semiring
open import semiring.exponentiation

module _
  {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {LO : isLinearOrder D<}
  {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
  {{AG : AdditiveGroup ACM}}
  {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
  {{LOS : LinearlyOrderedSemiringStr S LO}}
  {{SOS : StronglyLinearlyOrderedSemiringStr S LO}}
  where
  private
    instance ILO = LO
    instance IAG = AG
    instance IACM = ACM
    instance IS = S
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      ITA = isLinearOrder->isTightApartness-<> LO

  private
    diff-ends-pif : (n : Nat) -> (PolyIndex (suc n) -> D)
    diff-ends-pif n = ends-pif n 1# (- 1#)

    shift-ones-path : (n : Nat) ->
      Path (PolyIndex (suc n) -> D)
           (\pi -> (diff (shift₁ (all-ones-pif n) pi) (shift₂ (all-ones-pif n) pi)))
           (diff-ends-pif n)
    shift-ones-path n = funExt cases
      where
      cases : ∀ pi -> (diff (shift₁ (all-ones-pif n) pi) (shift₂ (all-ones-pif n) pi)) ==
                      diff-ends-pif n pi
      cases (zero    , zero    , p) = bot-elim (zero-suc-absurd p)
      cases (zero    , (suc j) , _) = +-right (minus-zero) >=> +-right-zero
      cases ((suc i) , zero    , _) = +-left-zero
      cases ((suc i) , (suc j) , _) = +-inverse

    module _ (x y : D) where
      diff-ends-eval-path : (n : Nat) ->
        finiteSum (eval-PI x y (diff-ends-pif n)) ==
        diff (x ^ℕ (suc n)) (y ^ℕ (suc n))
      diff-ends-eval-path n =
        ends-eval-path n 1# (- 1#) x y >=>
        +-cong *-left-one (minus-extract-left >=> cong -_ *-left-one)

      final-path : {n : Nat} ->
        diff (x ^ℕ (suc n)) (y ^ℕ (suc n)) ==
        (diff x y) * (finiteSum (eval-PI x y (all-ones-pif n)))
      final-path {n} =
        sym (diff-ends-eval-path n) >=>
        (\i -> finiteSum (eval-PI x y (shift-ones-path n (~ i)))) >=>
        (\i -> finiteSum (eval-diff-path x y
                           (suc n) (shift₁ (all-ones-pif n)) (shift₂ (all-ones-pif n)) i)) >=>
        finiteSum-diff >=>
        (\i -> diff (shift₁-eval-path x y (all-ones-pif n) i)
                    (shift₂-eval-path x y (all-ones-pif n) i)) >=>
        sym *-distrib-diff-right

  module _ (x y : D) (n : Nat) (en : Even n)
    (0<all-ones : x <> y -> 0# < finiteSum (eval-PI x y (all-ones-pif n))) where
    same-lt : Iso (x < y) ((x ^ℕ (suc n)) < (y ^ℕ (suc n)))
    same-lt = (diff-iso >iso> same-pos) >iso> (iso⁻¹ diff-iso)
      where
      diff-iso : {x y : D} -> Iso (x < y) (0# < diff x y)
      diff-iso = iso diff-0<⁺ diff-0<⁻ (\_ -> isProp-< _ _) (\_ -> isProp-< _ _)

      same-pos : Iso (0# < diff x y) (0# < diff (x ^ℕ (suc n)) (y ^ℕ (suc n)))
      same-pos .Iso.fun 0<d =
        trans-<-= (*-preserves-0< 0<d (0<all-ones (inj-l (diff-0<⁻ 0<d))))
                  (sym (final-path x y))
      same-pos .Iso.inv 0<d =
        *₂-reflects-0< 0<prod (asym-< (0<all-ones x<>y))
        where
        0<prod : 0# < (diff x y * (finiteSum (eval-PI x y (all-ones-pif n))))
        0<prod = trans-<-= 0<d (final-path x y)
        diff<>0 : diff x y <> 0#
        diff<>0 = proj₁ (*-reflects-<>0 (inj-r 0<prod))
        x<>y : x <> y
        x<>y = case diff<>0 of
          (\{ (inj-l d<0) -> inj-r (diff-<0⁻ d<0)
            ; (inj-r 0<d) -> inj-l (diff-0<⁻ 0<d)
            })
      same-pos .Iso.leftInv _ = isProp-< _ _
      same-pos .Iso.rightInv _ = isProp-< _ _
