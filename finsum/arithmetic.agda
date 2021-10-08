{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.arithmetic where

open import additive-group using (AdditiveCommMonoid)
open import base
open import commutative-monoid
open import equality
open import finite-commutative-monoid.instances
open import finset
open import finsum
open import semiring

module _ {ℓD ℓI : Level} {D : Type ℓD} {I : Type ℓI}
         {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} {{FI : FinSetStr I}}
  where
  private
    module S = Semiring S
    instance
      IACM = ACM

  abstract
    finiteSum-* : {k : D} {f : I -> D} -> finiteSum (\i -> k * (f i)) == k * finiteSum f
    finiteSum-* = finiteMerge-homo-inject _ _ k*ʰ
      where
      k*ʰ : {k : D} -> CommMonoidʰᵉ S.+-CommMonoid S.+-CommMonoid (k *_)
      k*ʰ {k} = record
        { preserves-ε = *-right-zero
        ; preserves-∙ = \_ _ -> *-distrib-+-left
        }
