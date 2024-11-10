{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.unique-entries where

open import base
open import container.finmap
open import container.finmap.all-entries
open import cubical
open import equivalence
open import equality
open import relation
open import truncation
open import finitely-indexed
open import finitely-indexed.order
open import sigma.base
open import order
open import order.instances.nat
open import maybe

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  UniqueEntries : Pred (FinMap' K V)  _
  UniqueEntries m = Σ[ k ∈ K ] Σ[ v ∈ V ] ∥ (HasKV' k v m) ∥

  private
    ℓKV = ℓ-max ℓK ℓV

    All->Unique : {m : FinMap' K V} -> AllEntries m -> UniqueEntries m
    All->Unique (k , v , hkv) = k , v , ∣ hkv ∣

    A->U : (m : FinMap' K V) -> AllEntries m -> UniqueEntries m
    A->U m = All->Unique {m}

    sur-All->Unique : {m : FinMap' K V} -> isSurjective (A->U m)
    sur-All->Unique (k , v , mhkv) =
      ∥-map (\hkv -> (k , v , hkv) , (\i -> k , v , squash ∣ hkv ∣ mhkv i)) mhkv

  isKFinSet-UniqueEntries : (m : FinMap' K V) -> isKFinSet (UniqueEntries m) ℓKV
  isKFinSet-UniqueEntries m = ∣ FinSet-AllEntries m , All->Unique , sur-All->Unique ∣

  KFinSet-UniqueEntries : (m : FinMap' K V) -> KFinSet⁻ ℓKV
  KFinSet-UniqueEntries m = UniqueEntries m , eqInv isKFinSet⁻-eq (isKFinSet-UniqueEntries m)


  module _ (m1 m2 : FinMap' K V) where
    private
      F : Type ℓKV
      F = (∀ k v -> (∥ HasKV' k v m2 ∥)-> Maybe (∥ HasKV' k v m1 ∥))

      module _ (f : F) where
        l : UniqueEntries m2 -> Maybe (UniqueEntries m1)
        l (k , v , hkv) = maybe-map (\hkv -> k , v , hkv) (f k v hkv)

    fm⊂3' : Type ℓKV
    fm⊂3' = ∃[ f ∈ F ] isSurjective (l f)

    fm⊂3'->HasKV : fm⊂3' -> {k : K} {v : V} -> HasKV' k v m1 -> ∥ HasKV' k v m2 ∥
    fm⊂3'->HasKV m1<m2 {k} {v} hkv = ∥-bind handle m1<m2
      where
      handle : Σ[ f ∈ F ] isSurjective (l f) -> ∥ HasKV' k v m2 ∥
      handle (f , sur-lf) = ∥-bind handle2 (sur-lf e)
        where
        e : Maybe (UniqueEntries m1)
        e = (just (k , v , ∣ hkv ∣))
        handle2 : fiber (l f) e -> ∥ HasKV' k v m2 ∥
        handle2 ((k2 , v2 , hkv2) , p) =
          subst2 (\k v -> ∥ HasKV' k v m2 ∥) kp vp hkv2
          where
          kp : k2 == k
          kp with (f k2 v2 hkv2)
          ... | (just hkv') = cong fst (just-injective p)
          ... | (nothing) = bot-elim (just!=nothing (sym p))

          vp : v2 == v
          vp with (f k2 v2 hkv2)
          ... | (just hkv') = \ i -> fst (snd (just-injective p i))
          ... | (nothing) = bot-elim (just!=nothing (sym p))

--    fm⊂3'->UniqueEntries< :
--      fm⊂3' ->
--      KFinSet< (KFinSet-UniqueEntries m1) (KFinSet-UniqueEntries m2)
--    fm⊂3'->UniqueEntries< m1⊂m2 n idx-U2 = (∥-bind handle m1⊂m2)
--      where
--      handle : Σ[ f ∈ F ] isSurjective (l f) ->
--               ∃[ m ∈ Nat ] (m < n × isIndexable (UniqueEntries m1) m)
--      handle (f , sur-lf) = ?



--  private
--    fm⊂->UniqueEntries< :
--      (m1 m2 : FinMap' K V) ->
--      m1 fm⊂ m2 ->
--      KFinSet< (KFinSet-UniqueEntries m1) (KFinSet-UniqueEntries m2)
--    fm⊂->UniqueEntries< m1 m2 m1<m2 zero ind-U2 =
--      bot-elim (eqFun U2≃Bot e)
--      where
--      U2≃Bot : UniqueEntries m2 ≃ Bot
--      U2≃Bot = isZeroIndexable-eq ind-U2
--
--      e : UniqueEntries m2
--      e = Σ-map (\k -> Σ-map (\v p -> ∣ snd p ∣)) (snd m1<m2)
--    fm⊂->UniqueEntries< m1 m2 m1<m2 (suc n) = ?
