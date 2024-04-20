{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.exponentiation.poly-index.ends where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical
open import equality-path
open import hlevel
open import finset.detachable
open import finsum
open import finite-commutative-monoid.partition
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import isomorphism
open import nat
open import ordered-ring.exponentiation.poly-index
open import ordered-ring.exponentiation.poly-index.eval
open import relation
open import sigma.base
open import subset
open import semiring
open import semiring.exponentiation


module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}} where
  ends-pif : (n : Nat) (x y : D) -> (PolyIndex (suc n) -> D)
  ends-pif _ x y (zero    , zero    , p) = bot-elim (zero-suc-absurd p)
  ends-pif _ x y (zero    , (suc j) , _) = x
  ends-pif _ x y ((suc i) , zero    , _) = y
  ends-pif _ x y ((suc i) , (suc j) , _) = 0#

private
  isEndIndex : (n : Nat) -> Subtype (PolyIndex (suc n)) ℓ-zero
  isEndIndex _ (zero    , zero    , p) = Bot , isPropBot
  isEndIndex _ (zero    , (suc j) , _) = Top , isPropTop
  isEndIndex _ ((suc i) , zero    , _) = Top , isPropTop
  isEndIndex _ ((suc i) , (suc j) , _) = Bot , isPropBot

  Det-isEndIndex : {n : Nat} -> Detachable (isEndIndex n)
  Det-isEndIndex (zero    , zero    , p) = bot-elim (zero-suc-absurd p)
  Det-isEndIndex (zero    , (suc j) , _) = yes tt
  Det-isEndIndex ((suc i) , zero    , _) = yes tt
  Det-isEndIndex ((suc i) , (suc j) , _) = no \x -> x

  EndIndex<->Boolean : {n : Nat} -> Iso (∈-Subtype (isEndIndex n)) Boolean
  EndIndex<->Boolean .Iso.fun ((zero    , (suc j) , _) , _) = true
  EndIndex<->Boolean .Iso.fun (((suc i) , zero    , _) , _) = false
  EndIndex<->Boolean {n} .Iso.inv true = (zero , suc n , refl) , tt
  EndIndex<->Boolean {n} .Iso.inv false = (suc n , zero , +-right-zero) , tt
  EndIndex<->Boolean .Iso.leftInv ((zero    , (suc j) , p) , _) =
    ΣProp-path (\{pi} -> snd (isEndIndex _ pi))
      (\i -> (zero , p (~ i) , (\j -> p (j ∨ (~ i)))))
  EndIndex<->Boolean {n} .Iso.leftInv (((suc i) , zero    , p) , _) =
    ΣProp-path (\{pi} -> snd (isEndIndex _ pi))
      (\k -> ((sym p >=> +-right-zero) k , zero ,
              isProp->PathPᵉ (\k' -> isSetNat ((sym p >=> +-right-zero) k' + 0#) (suc n))
                +-right-zero p k))
  EndIndex<->Boolean .Iso.rightInv true = refl
  EndIndex<->Boolean .Iso.rightInv false = refl


module _
  {ℓD : Level} {D : Type ℓD}
  {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
  where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      IACM = ACM

  module _ (n : Nat) (a b : D) (x y : D) where
    open FinSetStr-DetachableInstances (isEndIndex n) Det-isEndIndex

    ends-eval-path : finiteSum (eval-PI x y (ends-pif n a b)) ==
                     a * (y ^ℕ (suc n)) + b * (x ^ℕ (suc n))
    ends-eval-path =
      finiteMerge-detachable CM (isEndIndex n) Det-isEndIndex _ >=>
      +-right (finiteMerge-ε CM inner-zero) >=>
      +-right-zero >=>
      finiteMerge-2elem CM EndIndex<->Boolean _ >=>
      +-cong left-side right-side
      where
      inner-zero : ((pi , _) : (∉-Subtype (isEndIndex n))) ->
                   eval-PI x y (ends-pif n a b) pi == 0#
      inner-zero ((zero  , zero  , p) , _)    = bot-elim (zero-suc-absurd p)
      inner-zero ((zero  , suc j , _) , ¬end) = bot-elim (¬end tt)
      inner-zero ((suc i , zero  , _) , ¬end) = bot-elim (¬end tt)
      inner-zero ((suc i , suc j , _) , _)    = *-left-zero

      left-side : _ == a * (y ^ℕ (suc n))
      left-side = *-right *-left-one
      right-side : _ == b * (x ^ℕ (suc n))
      right-side = *-right *-right-one
