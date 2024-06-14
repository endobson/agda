{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.dense-extension where

open import base
open import metric-space
open import metric-space.subset
open import metric-space.complete
open import metric-space.continuous
open import metric-space.instances.subspace
open import subset
open import subset.subspace
open import relation
open import real.subspace
open import truncation hiding (Dense)

-- module _ {ℓA ℓB ℓS : Level} {A : Type ℓA} {B : Type ℓB}
--          {{MS-A : MetricSpaceStr A}}
--          {{MS-B : MetricSpaceStr B}} {S : Subtype A ℓS}
--          (dense : Dense S)
--          (isComplete-B : isComplete B)
--          (f : Subspace S -> B) (cf : isContinuous f) (x : A) where
--
--
--   extend-dense : B
--   extend-dense = ?
