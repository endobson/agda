{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.partition where

open import base
open import cubical
open import commutative-monoid
open import equality
open import isomorphism
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.sigma
open import finset
open import finset.detachable
open import finset.partition
open import finset.instances
open import finsum
open import functions
open import hlevel
open import relation
open import subset
open import type-algebra



module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) (isSet-D : isSet D) where
  open CommMonoid CM

  private
    finiteMergeᵉ' = finiteMergeᵉ CM
    finiteMerge' = finiteMerge CM
    finiteMerge'-convert = finiteMerge-convert CM

  module _ {ℓB ℓP : Level} (FB : FinSet ℓB) (partition : FinitePartition ⟨ FB ⟩ ℓP) where
    private
      B = fst FB
      isFinSet-B = snd FB

      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record {isFin = isFinSet-B}

      n = fst partition
      part : (i : Fin n) -> Subtype B ℓP
      part = fst (snd partition)

      part-rev : (b : B) -> Subtype (Fin n) ℓP
      part-rev b i = part i b

      P : (i : Fin n) -> Type _
      P i = ∈-Subtype (part i)

      P-rev : (b : B) -> Type _
      P-rev b = ∈-Subtype (part-rev b)

      isContr-P-rev : (b : B) -> isContr (P-rev b)
      isContr-P-rev = snd (snd partition)

      B≃ΣP-rev : B ≃ (Σ B P-rev)
      B≃ΣP-rev = Σ-isContr-eq isContr-P-rev

      ΣP-rev≃ΣP : (Σ B P-rev) ≃ (Σ (Fin n) P)
      ΣP-rev≃ΣP = Σ-swap-eq

      FP : (i : Fin n) -> FinSet _
      FP = FinSet-partition FB partition

    abstract
      finiteMerge-partition :
        (f : B -> D) ->
        finiteMerge' f ==
        finiteMerge' (\i -> (finiteMergeᵉ' (FP i) (f ∘ fst)))
      finiteMerge-partition f =
        finiteMerge'-convert FB (FinSet-Σ (FinSet-Fin n) FP) (equiv⁻¹ (B≃ΣP-rev >eq> ΣP-rev≃ΣP)) f >=>
        finiteMerge-Σ CM isSet-D (FinSet-Fin n) FP (\x -> f (fst (snd x)))

  module _ {ℓB ℓP : Level} (FB : FinSet ℓB) (partition : BinaryPartition ⟨ FB ⟩ ℓP) where
    private
      B = fst FB
      isFinSet-B = snd FB

      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record {isFin = isFinSet-B}

      k0 : Fin 2
      k0 = zero-fin
      k1 : Fin 2
      k1 = suc-fin zero-fin

      FP' : (i : Fin 2) -> FinSet (ℓ-max* 2 ℓB ℓP)
      FP' = FinSet-partition FB (2 , partition)

    abstract
      finiteMerge-binary-partition :
        (f : B -> D) ->
        finiteMerge' f ==
        (finiteMergeᵉ' (FP' k0) (f ∘ fst)) ∙ (finiteMergeᵉ' (FP' k1) (f ∘ fst))
      finiteMerge-binary-partition f =
        finiteMerge-partition FB (2 , partition) f >=>
        finiteMerge-Fin2 CM (\k -> (finiteMergeᵉ' (FP' k) (f ∘ fst)))
