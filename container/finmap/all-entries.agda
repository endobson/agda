{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.all-entries where

open import base
open import container.finmap
open import cubical
open import equality
open import equivalence
open import fin-algebra
open import finset
open import isomorphism
open import relation
open import truncation
open import maybe

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  AllEntries : Pred (FinMap' K V)  _
  AllEntries m = Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m)

  private
    ℓKV = ℓ-max ℓK ℓV

    hasKV-index : {k : K} {v : V} {m : FinMap' K V} -> (HasKV' k v m) -> FinT (fm'-size m)
    hasKV-index (has-kv-here _ _ _) = inj-l tt
    hasKV-index (has-kv-skip _ _ hkv) = inj-r (hasKV-index hkv)

    entry->index : {m : FinMap' K V} -> AllEntries m -> FinT (fm'-size m)
    entry->index (_ , _ , hkv) = hasKV-index hkv

    entry-skip : {m : FinMap' K V} (k2 : K) (v2 : V) ->
                 AllEntries m ->
                 AllEntries (fm-cons k2 v2 m)
    entry-skip k2 v2 (k , v , hk) = k , v , has-kv-skip k2 v2 hk

    index->entry : (m : FinMap' K V) -> FinT (fm'-size m) -> AllEntries m
    index->entry (fm-cons k v m) (inj-l tt) = k , v , has-kv-here refl refl m
    index->entry (fm-cons k v m) (inj-r i) = entry-skip k v (index->entry m i)

    ie-ei : (m : FinMap' K V) -> (e : AllEntries m) -> index->entry m (entry->index e) == e
    ie-ei (fm-cons k v m) (k2 , v2 , has-kv-here kp vp m) i = 
      kp (~ i) , vp (~ i) , has-kv-here (\j -> kp (j ∨ (~ i))) (\j -> vp (j ∨ (~ i))) m
    ie-ei (fm-cons k v m) (k2 , v2 , has-kv-skip kp vp hkv) = 
      cong (entry-skip k v) (ie-ei m (k2 , v2 , hkv))

    ei-ie : (m : FinMap' K V) -> (i : FinT (fm'-size m)) -> entry->index (index->entry m i) == i
    ei-ie (fm-cons k v m) (inj-l tt) = refl
    ei-ie (fm-cons k v m) (inj-r i) = cong inj-r (ei-ie m i)

  AllEntries-FinT-eq : (m : FinMap' K V) -> (AllEntries m) ≃ FinT (fm'-size m)
  AllEntries-FinT-eq m = isoToEquiv (iso entry->index (index->entry m) (ei-ie m) (ie-ei m))

  isFinSet-AllEntries : (m : FinMap' K V) -> isFinSet (AllEntries m)
  isFinSet-AllEntries m = ∣ _ , AllEntries-FinT-eq m >eq> pathToEquiv (FinT=Fin _) ∣

  FinSet-AllEntries : (m : FinMap' K V) -> FinSet ℓKV
  FinSet-AllEntries m = AllEntries m , isFinSet-AllEntries m

  _fm⊂2_ : Rel (FinMap' K V) ℓKV
  _fm⊂2_ m1 m2 = Σ (AllEntries m2 -> Maybe (AllEntries m1)) isSurjection

