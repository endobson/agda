{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.indicator where

open import additive-group
open import base
open import equality
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.partition
open import finset
open import finset.detachable
open import finsum
open import functions
open import funext
open import semiring
open import subset
open import subset.indicator
open import truncation

open EqReasoning

module _ {ℓD : Level} {D : Type ℓD}
         {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}}
         where
  private
    instance
      IACM = ACM

  module _ {ℓI ℓS : Level} {I : Type ℓI} (S : Subtype I ℓS) (DetS : Detachable S)
           {{FI : FinSetStr I}} {f : I -> D} where
    private
      f' : ∈-Subtype S -> D
      f' = f ∘ fst

      open FinSetStr-DetachableInstances S DetS

    abstract
      finiteSum-indicator : finiteSum f' == finiteSum (\i -> indicator S DetS i * f i)
      finiteSum-indicator =
        begin
          finiteSum f'
        ==< sym +-right-zero >=> sym (+-right (finiteMerge-ε _ (\_ -> refl))) >
          finiteSum f' + finiteSum z'
        ==< (\i -> finiteSum (f'=if i) + finiteSum (z'=if i)) >
          finiteSum (\(i , s) -> indicator S DetS i * f i) +
          finiteSum (\(i , ¬s) -> indicator S DetS i * f i)
        ==< sym (finiteMerge-detachable _ S DetS _) >
          finiteSum (\i -> indicator S DetS i * f i)
        end
        where
        z' : ∉-Subtype S -> D
        z' _ = 0#

        f'=if : f' == (\(i , s) -> indicator S DetS i * f i)
        f'=if = funExt (\(_ , s) -> sym *-left-one >=> *-left (sym (indicator-=1 s)))

        z'=if : z' == (\(i , ¬s) -> indicator S DetS i * f i)
        z'=if = funExt (\(_ , ¬s) -> sym *-left-zero >=> *-left (sym (indicator-=0 ¬s)))
