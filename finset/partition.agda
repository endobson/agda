{-# OPTIONS --cubical --safe --exact-split #-}

module finset.partition where

open import base
open import equality
open import fin
open import finset
open import finset.detachable
open import relation
open import subset


module _ {ℓB ℓS ℓP : Level} (FB : FinSet ℓB) (partition : FinitePartition ⟨ FB ⟩ ℓS ℓP) where
  private
    B = fst FB
    isFinSet-B = snd FB

    fS = fst partition
    S = fst fS
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


    Detachable-part : (i : S) -> Detachable (part i)
    Detachable-part i b = handle (isContr-P-rev b)
      where
      handle : isContr (P-rev b) -> Dec ⟨ part i b ⟩
      handle ((i2 , pib2) , path) = handle2 (isFinSet->Discrete (snd fS) i i2)
        where
        handle2 : Dec (i == i2) -> Dec ⟨ part i b ⟩
        handle2 (yes i-path) = yes (subst (\x -> ⟨ part x b ⟩) (sym i-path) pib2)
        handle2 (no ¬i-path) = no ¬pib
          where
          ¬pib : ¬ ⟨ part i b ⟩
          ¬pib pib = ¬i-path (sym (cong fst (path (_ , pib))))

  abstract
    isFinSet-partition : (i : S) -> isFinSet (P i)
    isFinSet-partition i = isFinSet-Detachable (part i) isFinSet-B (Detachable-part i)

  FinSet-partition : (i : S) -> FinSet _
  FinSet-partition i = P i , isFinSet-partition i
