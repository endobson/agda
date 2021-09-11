{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space.finite where

open import apartness
open import base
open import cubical using (_≃_)
open import commutative-monoid
open import equality hiding (J)
open import equivalence
open import fin
open import finset
open import finset.partition
open import finset.detachable
open import finsum
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.partition
open import functions
open import group
open import heyting-field
open import hlevel
open import monoid
open import ring
open import relation
open import semiring
open import subset
open import truncation
open import vector-space

private
  variable
    ℓ : Level

module _ {ℓK ℓV : Level} {K : Type ℓK} {{S : Semiring K}} {{R : Ring S}}
         {{A : TightApartnessStr K}} {{F : Field R A}} {V : Type ℓV}
         {{VS : VectorSpaceStr F V}} where


  private
    module VS = VectorSpaceStr VS
    module M = ModuleStr VS.module-str

    instance
      IM = VS.module-str
      IVA = ModuleStr.TightApartnessStr-V IM


  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    scaled-vector-sum : (I -> K) -> (I -> V) -> V
    scaled-vector-sum ks vs = vector-sum (\i -> (ks i) v* (vs i))


  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} (vs : I -> V) where
    LinearlyDependent :  Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyDependent =
      ∃[ a ∈ (I -> K) ] ((scaled-vector-sum a vs == 0v) × (Σ[ i ∈ I ] (a i # 0#)))

    LinearlyIndependent : Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyIndependent =
      (a : I -> K) ->
      scaled-vector-sum a vs == 0v ->
      (i : I) -> a i == 0#

    LinearlyFree : Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyFree =
      (a : I -> K) ->
      ∃[ i ∈ I ] ((a i) # 0#) ->
      scaled-vector-sum a vs # 0v


    LinearlyFree->LinearlyIndependent : LinearlyFree -> LinearlyIndependent
    LinearlyFree->LinearlyIndependent free a sum0 i =
      tight-# (\ai#0 -> irrefl-path-# sum0 (free a ∣ (i , ai#0) ∣))

    LinearlyIndependent->¬LinearlyDependent : LinearlyIndependent -> ¬ LinearlyDependent
    LinearlyIndependent->¬LinearlyDependent indep dep =
      unsquash isPropBot (∥-map handle dep)
      where
      handle : Σ[ a ∈ (I -> K) ] (scaled-vector-sum a vs == 0v ×
                                  Σ[ i ∈ I ] (a i # 0#)) -> Bot
      handle (a , sum0 , i , ai#0) = irrefl-path-# (indep a sum0 i) ai#0

    ¬LinearlyDependent->LinearlyIndependent : ¬ LinearlyDependent -> LinearlyIndependent
    ¬LinearlyDependent->LinearlyIndependent ¬dep a sum0 i =
      tight-# (\ai#0 -> ¬dep ∣ a , sum0 , i , ai#0 ∣)

    LinearlyDependent->¬LinearlyIndependent : LinearlyDependent -> ¬ LinearlyIndependent
    LinearlyDependent->¬LinearlyIndependent dep indep =
      LinearlyIndependent->¬LinearlyDependent indep dep

    ¬LinearlyIndependent->¬LinearlyFree : ¬ LinearlyIndependent -> ¬ LinearlyFree
    ¬LinearlyIndependent->¬LinearlyFree ¬indep free =
      ¬indep (LinearlyFree->LinearlyIndependent free)

    isLinearCombination : Pred V _
    isLinearCombination v =
      ∃[ a ∈ (I -> K) ] (scaled-vector-sum a vs == v)

    LinearSpan : Subtype V (ℓ-max* 3 ℓK ℓV ℓI)
    LinearSpan v = isLinearCombination v , squash


    isAffineCombination : Pred V _
    isAffineCombination v =
      ∃[ a ∈ (I -> K) ] (scaled-vector-sum a vs == v ×
                         finiteSum (I , FinSetStr.isFin FI) a == 1#)

    AffineSpan : Subtype V (ℓ-max* 3 ℓK ℓV ℓI)
    AffineSpan v = isAffineCombination v , squash

    isSpanning : Type (ℓ-max* 3 ℓK ℓV ℓI)
    isSpanning = isFullSubtype LinearSpan

    isBasis : Type (ℓ-max* 3 ℓK ℓV ℓI)
    isBasis = isSpanning × LinearlyIndependent
