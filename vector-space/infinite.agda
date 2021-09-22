{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space.infinite where

open import additive-group
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

module _ {ℓK ℓV : Level} {K : Type ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : TightApartnessStr K} {F : Field R A} {V : Type ℓV}
         (VS : VectorSpaceStr F V) where

  private
    module VS = VectorSpaceStr VS
    module M = ModuleStr VS.module-str
    module R = Ring R
    module F = Field F

    instance
      IM = VS.module-str
      IACM = ACM
      IS = S
      IF = F
      IVA = ModuleStr.TightApartnessStr-V IM
      IFA = Field.TightApartnessStr-f# F
      IVS = VS


  private
    variable
      I : Type ℓ

  private
    CommMonoid-V+ : CommMonoid V
    CommMonoid-V+ = GroupStr.comm-monoid M.GroupStr-V


  private
    module _ {ℓI₁ : Level} {I₁ : Type ℓI₁} where
      Carrier : {ℓI₂ : Level} -> FinSubset I₁ ℓI₂ -> Type ℓI₂
      Carrier ((T , _) , _) = T

      isFinSet-Carrier : {ℓI₂ : Level} -> (S : FinSubset I₁ ℓI₂) -> isFinSet (Carrier S)
      isFinSet-Carrier ((_ , fs) , _) = fs

      include : {ℓI₂ : Level} -> (S : FinSubset I₁ ℓI₂) -> Carrier S -> I₁
      include (_ , f , _) = f

  module _ {ℓI₁ ℓI₂ : Level} {I₁ : Type ℓI₁} (family : I₁ -> V) (S : FinSubset I₁ ℓI₂) where
    scaled-vector-sum-inner : (a : Carrier S -> K) -> Carrier S -> V
    scaled-vector-sum-inner a = (\i -> (a i) v* (family (include S i)))

    scaled-vector-sum : (a : Carrier S -> K) -> V
    scaled-vector-sum a = vector-sum (scaled-vector-sum-inner a)
      where
      instance
        FinSetStr-S : FinSetStr (Carrier S)
        FinSetStr-S = record {isFin = isFinSet-Carrier S}

  module _ {ℓI₁ : Level} {I₁ : Type ℓI₁} (family : I₁ -> V) where

    LinearlyDependent : (ℓI₂ : Level) -> Type (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
    LinearlyDependent ℓI₂ =
      ∃[ S ∈ FinSubset I₁ ℓI₂ ]
      Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == 0v ×
                                 Σ[ i ∈ Carrier S ] (a i # 0#))

    LinearlyIndependent : (ℓI₂ : Level) -> Type (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
    LinearlyIndependent ℓI₂ =
      (S : FinSubset I₁ ℓI₂) -> (a : Carrier S -> K) ->
      scaled-vector-sum family S a == 0v ->
      (i : Carrier S) -> a i == 0#

    LinearlyFree : (ℓI₂ : Level) -> Type (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
    LinearlyFree ℓI₂ =
      (S : FinSubset I₁ ℓI₂) -> (a : Carrier S -> K) ->
      ∃[ i ∈ Carrier S ] ((a i) # 0#) ->
      scaled-vector-sum family S a # 0v


    LinearlyFree->LinearlyIndependent : {ℓI₂ : Level} -> LinearlyFree ℓI₂ -> LinearlyIndependent ℓI₂
    LinearlyFree->LinearlyIndependent free S a sum0 i =
      tight-# (\ai#0 -> irrefl-path-# sum0 (free S a ∣ (i , ai#0) ∣))

    LinearlyIndependent->¬LinearlyDependent :
      {ℓI₂ : Level} -> LinearlyIndependent ℓI₂ -> ¬ (LinearlyDependent ℓI₂)
    LinearlyIndependent->¬LinearlyDependent {ℓI₂} indep dep =
      unsquash isPropBot (∥-map handle dep)
      where
      handle : Σ[ S ∈ FinSubset I₁ ℓI₂ ]
               Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == 0v ×
                                          Σ[ i ∈ Carrier S ] (a i # 0#)) -> Bot
      handle (S , a , sum0 , i , ai#0) = irrefl-path-# (indep S a sum0 i) ai#0

    ¬LinearlyDependent->LinearlyIndependent :
      {ℓI₂ : Level} -> ¬(LinearlyDependent ℓI₂) -> LinearlyIndependent ℓI₂
    ¬LinearlyDependent->LinearlyIndependent ¬dep S a sum0 i =
      tight-# (\ai#0 -> ¬dep ∣ S , a , sum0 , i , ai#0 ∣)

    LinearlyDependent->¬LinearlyIndependent :
      {ℓI₂ : Level} -> (LinearlyDependent ℓI₂) -> ¬ (LinearlyIndependent ℓI₂)
    LinearlyDependent->¬LinearlyIndependent dep indep =
      LinearlyIndependent->¬LinearlyDependent indep dep

    ¬LinearlyIndependent->¬LinearlyFree :
      {ℓI₂ : Level} -> ¬ (LinearlyIndependent ℓI₂) -> ¬ (LinearlyFree ℓI₂)
    ¬LinearlyIndependent->¬LinearlyFree ¬indep free =
      ¬indep (LinearlyFree->LinearlyIndependent free)

    module _ (ℓI₂ : Level) where
      isLinearCombination : Pred V _
      isLinearCombination v =
        ∃[ S ∈ FinSubset I₁ ℓI₂ ]
        Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == v)

      LinearSpan : Subtype V (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
      LinearSpan v = isLinearCombination v , squash

      isAffineCombination : Pred V _
      isAffineCombination v =
        ∃[ S ∈ FinSubset I₁ ℓI₂ ]
        Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == v ×
                                   finiteSumᵉ ⟨ S ⟩ a == 1#)

      AffineSpan : Subtype V (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
      AffineSpan v = isLinearCombination v , squash

      isSpanning : Type _
      isSpanning = isFullSubtype LinearSpan

      isBasis : Type _
      isBasis = isSpanning × LinearlyIndependent ℓI₂

  Basis : (ℓI : Level) -> Type _
  Basis ℓI = Σ[ I ∈ Type ℓI ] Σ[ family ∈ (I -> V) ] (isBasis family ℓI)
