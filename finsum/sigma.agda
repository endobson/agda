{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.sigma where

open import additive-group
open import base
open import equality-path
open import finite-commutative-monoid.sigma
open import finset
open import finset.instances.sigma
open import finsum
open import finsum.arithmetic
open import funext
open import semiring

module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}
  {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
  {{FS-A : FinSetStr A}} {{FS-B : FinSetStr B}}
  {{S : Semiring ACM}}
  where

  opaque
    finiteSum-× : {f : A -> D} {g : B -> D} ->
      finiteSum (\ ((a , b) : A × B) -> f a * g b) ==
      finiteSum f * finiteSum g
    finiteSum-× =
      finiteMergeᵉ-Σ (A , isFinSetⁱ) (\_ -> (B , isFinSetⁱ)) >=>
      cong finiteSum (funExt (\a ->
        finiteSum-* >=> *-commute)) >=>
      finiteSum-* >=> *-commute
