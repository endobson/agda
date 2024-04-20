{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.partition where

open import base
open import commutative-monoid
open import equality
open import equivalence
open import isomorphism
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.sigma
open import finset
open import finset.partition
open import finset.instances
open import finset.instances.boolean
open import finset.instances.sigma
open import finset.detachable
open import functions
open import subset
open import type-algebra



module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  private
    finiteMergeᵉ' = finiteMergeᵉ CM
    finiteMerge' = finiteMerge CM

  module _ {ℓB ℓS ℓP : Level} {B : Type ℓB} {{FinSetStr-B : FinSetStr B}}
           (partition : FinitePartition B ℓS ℓP) where
    private
      FB : FinSet ℓB
      FB = B , isFinSetⁱ
      fS = fst partition
      S = fst fS

      instance
        iFS : FinSetStr S
        iFS = record {isFin = snd fS}

      part : (i : S) -> Subtype B ℓP
      part = fst (snd partition)

      part-rev : (b : B) -> Subtype S ℓP
      part-rev b i = part i b

      P : (i : S) -> Type _
      P i = ∈-Subtype (part i)

      P-rev : (b : B) -> Type _
      P-rev b = ∈-Subtype (part-rev b)

      isContr-P-rev : (b : B) -> isContr (P-rev b)
      isContr-P-rev = snd (snd partition)

      B≃ΣP-rev : B ≃ (Σ B P-rev)
      B≃ΣP-rev = Σ-isContr-eq isContr-P-rev

      ΣP-rev≃ΣP : (Σ B P-rev) ≃ (Σ S P)
      ΣP-rev≃ΣP = Σ-swap-eq

      FP : (i : S) -> FinSet _
      FP = FinSet-partition FB partition

    abstract
      finiteMerge-partition :
        (f : B -> D) ->
        finiteMerge' f ==
        finiteMerge' (\i -> (finiteMergeᵉ' (FP i) (f ∘ fst)))
      finiteMerge-partition f =
        finiteMergeᵉ-convert CM FB (FinSet-Σ fS FP) (equiv⁻¹ (B≃ΣP-rev >eq> ΣP-rev≃ΣP)) f >=>
        finiteMerge-Σ CM fS FP (\x -> f (fst (snd x)))

  module _ {ℓB ℓS ℓP : Level}
           {B : Type ℓB} {{FinSetStr-B : FinSetStr B}}
           (bin-partition : BinaryPartition B ℓS ℓP)
           (f : B -> D)
           where
    private
      FB : FinSet ℓB
      FB = B , isFinSetⁱ
      partition = fst bin-partition
      FS = fst partition
      S = fst FS

      FP' : (b : Boolean) -> FinSet (ℓ-max* 2 ℓB ℓP)
      FP' b = FinSet-partition FB partition (eqInv (snd bin-partition) b)

      f₁ : ⟨ FP' true ⟩ -> D
      f₁ (i , _) = f i
      f₂ : ⟨ FP' false ⟩ -> D
      f₂ (i , _) = f i

      instance
        iFS : FinSetStr S
        iFS = record {isFin = snd FS}

    abstract
      finiteMerge-binary-partition :
        finiteMerge' f ==
        (finiteMergeᵉ' (FP' true) f₁) ∙ (finiteMergeᵉ' (FP' false) f₂)
      finiteMerge-binary-partition =
        finiteMerge-partition partition f >=>
        finiteMerge-convert CM (equiv⁻¹ (snd bin-partition)) _ >=>
        finiteMerge-Boolean CM (\k -> (finiteMergeᵉ' (FP' k) (f ∘ fst)))

  module _ {ℓI ℓS : Level} {I : Type ℓI} {{FinSetStr-I : FinSetStr I}}
           (S : Subtype I ℓS) (DetS : Detachable S)
           {{FinSetStr-∈ : FinSetStr (∈-Subtype S)}}
           {{FinSetStr-∉ : FinSetStr (∉-Subtype S)}}
           (f : I -> D) where
    private
      FI : FinSet ℓI
      FI = I , isFinSetⁱ

      f₁ : (∈-Subtype S) -> D
      f₁ (i , _) = f i
      f₂ : (∉-Subtype S) -> D
      f₂ (i , _) = f i

    abstract
      finiteMerge-detachable : finiteMerge' f == finiteMerge' f₁ ∙ finiteMerge' f₂
      finiteMerge-detachable =
        finiteMerge-binary-partition (Detachable->BinaryPartition S DetS) f >=>
        cong2 (\fs1 fs2 -> finiteMergeᵉ' (_ , fs1) f₁ ∙ finiteMergeᵉ' (_ , fs2) f₂)
              (isProp-isFinSet _ _) (isProp-isFinSet _ _)
