{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module container.finmap.partition-keys where

open import base
open import container.finmap
open import equality
open import functions
open import hlevel
open import nat.order
open import order
open import order.instances.nat
open import sigma.base
open import relation

module _ {ℓK : Level} {ℓV : Level} {K : Type ℓK} {V : Type ℓV}  where

  module _ {ℓ : Level} {P : Pred K ℓ} (d : Decidable P) where

    finmap'-partition-keys : FinMap' K V -> FinMap' K V × FinMap' K V
    finmap'-partition-keys [] = [] , []
    finmap'-partition-keys (fm-cons k v m) = handle (d k)
      where
      handle : Dec (P k) -> FinMap' K V × FinMap' K V
      handle (yes _) = ×-map (fm-cons k v) (\x -> x) (finmap'-partition-keys m)
      handle (no _) = ×-map (\x -> x) (fm-cons k v) (finmap'-partition-keys m)

    finmap'-keep-keys : FinMap' K V -> FinMap' K V
    finmap'-keep-keys = fst ∘ finmap'-partition-keys
    finmap'-drop-keys : FinMap' K V -> FinMap' K V
    finmap'-drop-keys = snd ∘ finmap'-partition-keys


    HasKey-finmap'-keep-keys :
      {m : FinMap' K V} -> {k : K} -> P k -> HasKey' k m -> (HasKey' k (finmap'-keep-keys m))
    HasKey-finmap'-keep-keys {m = fm-cons k2 v2 m} p (v , has-kv-here k=k2 vp _) with (d k2)
    ... | (yes _) = v , has-kv-here k=k2 vp _
    ... | (no ¬p) = bot-elim (¬p (subst P k=k2 p))
    HasKey-finmap'-keep-keys p (v , has-kv-skip k2 v2 hkv) with (d k2)
    ... | (yes _) = HasKey'-skip (HasKey-finmap'-keep-keys p (v , hkv))
    ... | (no _) = HasKey-finmap'-keep-keys p (v , hkv)

    HasKey-finmap'-drop-keys :
      {m : FinMap' K V} -> {k : K} -> ¬ (P k) -> HasKey' k m -> (HasKey' k (finmap'-drop-keys m))
    HasKey-finmap'-drop-keys {m = fm-cons k2 v2 m} ¬p (v , has-kv-here k=k2 vp _) with (d k2)
    ... | (no _) = v , has-kv-here k=k2 vp _
    ... | (yes p) = bot-elim (¬p (subst P (sym k=k2) p))
    HasKey-finmap'-drop-keys ¬p (v , has-kv-skip k2 v2 hkv) with (d k2)
    ... | (no _) = HasKey'-skip (HasKey-finmap'-drop-keys ¬p (v , hkv))
    ... | (yes _) = HasKey-finmap'-drop-keys ¬p (v , hkv)

    ¬HasKey-finmap'-keep-keys :
      {m : FinMap' K V} {k : K} -> (¬p : ¬ (P k)) -> ¬ (HasKey' k (finmap'-keep-keys m))
    ¬HasKey-finmap'-keep-keys {[]} _ ()
    ¬HasKey-finmap'-keep-keys {fm-cons k v m} {ik} ¬p with (d k)
    ... | (no _) = ¬HasKey-finmap'-keep-keys {m} ¬p
    ... | (yes p) = handle
      where
      handle : ¬ (HasKey' ik (fm-cons k v (finmap'-keep-keys m)))
      handle (_ , has-kv-here kp _ _) = ¬p (subst P (sym kp) p)
      handle (v , has-kv-skip _ _ hkv) = ¬HasKey-finmap'-keep-keys {m} ¬p (v , hkv)

    ¬HasKey-finmap'-drop-keys :
      {m : FinMap' K V} {k : K} -> (P k) -> ¬ (HasKey' k (finmap'-drop-keys m))
    ¬HasKey-finmap'-drop-keys {[]} _ ()
    ¬HasKey-finmap'-drop-keys {fm-cons k v m} {ik} p with (d k)
    ... | (yes _) = ¬HasKey-finmap'-drop-keys {m} p
    ... | (no ¬p) = handle
      where
      handle : ¬ (HasKey' ik (fm-cons k v (finmap'-drop-keys m)))
      handle (_ , has-kv-here kp _ _) = ¬p (subst P kp p)
      handle (v , has-kv-skip _ _ hkv) = ¬HasKey-finmap'-drop-keys {m} p (v , hkv)

    fm⊆-finmap'-keep-keys : (m : FinMap' K V) -> finmap'-keep-keys m fm⊆ m
    fm⊆-finmap'-keep-keys (fm-cons k2 v2 m) hkv with (d k2) | hkv
    ... | (yes _) | (has-kv-here kp vp _) = has-kv-here kp vp _
    ... | (yes _) | (has-kv-skip _ _ hkv) = has-kv-skip _ _ (fm⊆-finmap'-keep-keys m hkv)
    ... | (no _)  | hkv = has-kv-skip _ _ (fm⊆-finmap'-keep-keys m hkv)

    fm⊆-finmap'-drop-keys : (m : FinMap' K V) -> finmap'-drop-keys m fm⊆ m
    fm⊆-finmap'-drop-keys (fm-cons k2 v2 m) hkv with (d k2) | hkv
    ... | (no _)  | (has-kv-here kp vp _) = has-kv-here kp vp _
    ... | (no _)  | (has-kv-skip _ _ hkv) = has-kv-skip _ _ (fm⊆-finmap'-drop-keys m hkv)
    ... | (yes _) | hkv = has-kv-skip _ _ (fm⊆-finmap'-drop-keys m hkv)


    fm'-size-finmap'-keep-keys : (m : FinMap' K V) -> fm'-size (finmap'-keep-keys m) ≤ fm'-size m
    fm'-size-finmap'-keep-keys [] = refl-≤
    fm'-size-finmap'-keep-keys (fm-cons k v m) with (d k)
    ... | (yes _) = suc-≤ (fm'-size-finmap'-keep-keys m)
    ... | (no _) = right-suc-≤ (fm'-size-finmap'-keep-keys m)

    fm'-size-finmap'-drop-keys : (m : FinMap' K V) -> fm'-size (finmap'-drop-keys m) ≤ fm'-size m
    fm'-size-finmap'-drop-keys [] = refl-≤
    fm'-size-finmap'-drop-keys (fm-cons k v m) with (d k)
    ... | (yes _) = right-suc-≤ (fm'-size-finmap'-drop-keys m)
    ... | (no _) = suc-≤ (fm'-size-finmap'-drop-keys m)


    fm'-size-finmap'-keep-keys-strict :
      {k : K} {v : V} -> (m : FinMap' K V) -> HasKV' k v m -> ¬ (P k) ->
      fm'-size (finmap'-keep-keys m) < fm'-size m
    fm'-size-finmap'-keep-keys-strict (fm-cons k v m) (has-kv-here kp vp hkv) ¬p with (d k)
    ... | (yes p) = bot-elim (¬p (subst P (sym kp) p))
    ... | (no _) = suc-≤ (fm'-size-finmap'-keep-keys m)
    fm'-size-finmap'-keep-keys-strict (fm-cons k v m) (has-kv-skip _ _ hkv) ¬p with (d k)
    ... | (yes _) = suc-≤ (fm'-size-finmap'-keep-keys-strict m hkv ¬p)
    ... | (no _) = right-suc-≤ (fm'-size-finmap'-keep-keys-strict m hkv ¬p)

