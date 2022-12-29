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
open import finsum
open import functions
open import subset
open import type-algebra



module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  private
    finiteMergeᵉ' = finiteMergeᵉ CM
    finiteMerge' = finiteMerge CM

  module _ {ℓB ℓS ℓP : Level} (FB : FinSet ℓB) (partition : FinitePartition ⟨ FB ⟩ ℓS ℓP) where
    private
      B = fst FB
      isFinSet-B = snd FB

      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record {isFin = isFinSet-B}


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

  module _ {ℓB ℓS ℓP : Level} (FB : FinSet ℓB) (bin-partition : BinaryPartition ⟨ FB ⟩ ℓS ℓP) where
    private
      B = fst FB
      isFinSet-B = snd FB

      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record {isFin = isFinSet-B}

      partition = fst bin-partition
      FS = fst partition
      S = fst FS

      FP' : (b : Boolean) -> FinSet (ℓ-max* 2 ℓB ℓP)
      FP' b = FinSet-partition FB partition (eqInv (snd bin-partition) b)

    abstract
      finiteMerge-binary-partition :
        (f : B -> D) ->
        finiteMerge' f ==
        (finiteMergeᵉ' (FP' true) (f ∘ fst)) ∙ (finiteMergeᵉ' (FP' false) (f ∘ fst))
      finiteMerge-binary-partition f =
        finiteMerge-partition FB partition f >=>
        finiteMergeᵉ-convert CM _ _ (equiv⁻¹ (snd bin-partition)) _ >=>
        finiteMerge-Boolean CM (\k -> (finiteMergeᵉ' (FP' k) (f ∘ fst)))
