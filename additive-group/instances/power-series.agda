{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.power-series where

open import additive-group
open import base
open import power-series

module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}} where
  instance
    AdditiveCommMonoid-PS : AdditiveCommMonoid (PowerSeries D)
    AdditiveCommMonoid-PS = record
      { comm-monoid = record
        { monoid = record
          { ε = 0-PS
          ; _∙_ = +-PS
          ; ∙-assoc = +-PS-assoc
          ; ∙-left-ε = +-PS-left-zero
          ; ∙-right-ε = +-PS-right-zero
          ; isSet-Domain = isSet-PowerSeries (AdditiveCommMonoid.isSet-Domain ACM)
          }
        ; ∙-commute = +-PS-commute
        }
      }
      where
      0-PS : PowerSeries D
      0-PS = power-series (\_ -> 0#)
      +-PS : PowerSeries D -> PowerSeries D -> PowerSeries D
      +-PS (power-series x) (power-series y) = power-series (\i -> x i + y i)

      opaque
        +-PS-assoc : {a b c : PowerSeries D} -> (+-PS (+-PS a b) c) == (+-PS a (+-PS b c))
        +-PS-assoc {power-series sa} {power-series sb} {power-series sc} j =
          power-series (\i -> +-assocᵉ (sa i) (sb i) (sc i) j)
        +-PS-left-zero : {a : PowerSeries D} -> (+-PS 0-PS a) == a
        +-PS-left-zero {power-series s} j = power-series (\i -> +-left-zeroᵉ (s i) j)
        +-PS-right-zero : {a : PowerSeries D} -> (+-PS a 0-PS) == a
        +-PS-right-zero {power-series s} j = power-series (\i -> +-right-zeroᵉ (s i) j)
        +-PS-commute : {a b : PowerSeries D} -> (+-PS a b) == (+-PS b a)
        +-PS-commute {power-series sa} {power-series sb} j =
          power-series (\i -> +-commuteᵉ (sa i) (sb i) j)
