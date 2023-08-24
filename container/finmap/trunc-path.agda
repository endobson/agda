{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.trunc-path where

open import base
open import equality
open import equivalence
open import list
open import fin-algebra
open import truncation
open import set-quotient
open import relation
open import hlevel

record MapStructure {ℓK ℓV ℓM : Level}
       (K : Type ℓK) (V : Type ℓV) (M : Type ℓM) (ℓS : Level) :
       Type (ℓ-max (ℓ-max* 3 ℓK ℓV ℓM) (ℓ-suc ℓS)) where
  field
    Support : M -> K -> Type ℓS
    lookup : (m : M) -> (k : K) -> Support m k -> V

  lookup' : (m : M) -> Σ K (Support m) -> V
  lookup' m (k , s) = lookup m k s


record UniqueMapStructure {ℓK ℓV ℓM ℓS : Level}
       {K : Type ℓK} {V : Type ℓV} {M : Type ℓM}
       (MS : MapStructure K V M ℓS) :
       Type (ℓ-max (ℓ-max* 3 ℓK ℓV ℓM) (ℓ-suc ℓS)) where
  private
    module MS = MapStructure MS

  field
    unique-entries : (m : M) -> isContr (Image (MS.lookup' m))


record UniversalMapStructure {ℓK ℓV ℓM ℓS : Level}
       {K : Type ℓK} {V : Type ℓV} {M : Type ℓM}
       (MS : MapStructure K V M ℓS) :
       Type (ℓ-max (ℓ-max* 3 ℓK ℓV ℓM) (ℓ-suc ℓS)) where
  private
    module MS = MapStructure MS

  field
    supported-keys-eq :
      (m1 m2 : M) -> ((∀ k -> Image (MS.lookup m1 k) ≃ Image (MS.lookup m2 k)) ≃ (m1 == m2))

record PropEntriesMapStructure {ℓK ℓV ℓM ℓS : Level}
       {K : Type ℓK} {V : Type ℓV} {M : Type ℓM}
       (MS : MapStructure K V M ℓS) :
       Type (ℓ-max (ℓ-max* 3 ℓK ℓV ℓM) (ℓ-suc ℓS)) where
  private
    module MS = MapStructure MS

  field
    prop-entries : (m : M) (k : K) -> isProp (Image (MS.lookup m k))


record UpdatableMapStructure {ℓK ℓV ℓM ℓS : Level}
       {K : Type ℓK} {V : Type ℓV} {M : Type ℓM}
       (MS : MapStructure K V M ℓS) :
       Type (ℓ-max (ℓ-max* 3 ℓK ℓV ℓM) (ℓ-suc ℓS)) where
  private
    module MS = MapStructure MS

  field
    update : (m : M) -> (k : K) -> V -> M

    update-preserves-support :
      (m : M) (k : K) (v : V) -> (k2 : K) -> (MS.Support m k2) -> (MS.Support (update m k v) k2)
    update-supported :
      (m : M) (k : K) (v : V) -> (MS.Support (update m k v) k)
    update-lookup :
      (m : M) (k : K) (v : V) -> (s : MS.Support (update m k v) k) -> MS.lookup (update m k v) k s == v


    update-preserves-fibers :
      (m : M) (k : K) (v : V) ->
      (k2 : K) -> k != k2 -> (v2 : V) ->
      (fiber (MS.lookup m k2) v2 ≃ fiber (MS.lookup (update m k v) k2) v2)




FinMapRaw : {ℓK ℓV : Level} -> Type ℓK -> Type ℓV -> Type (ℓ-max ℓK ℓV)
FinMapRaw K V = List (K × V)

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  private
    Index : FinMapRaw K V -> Type₀
    Index m = FinT (length m)

    at-index : (m : FinMapRaw K V) -> Index m -> K × V
    at-index (e :: _) (inj-l _) = e
    at-index (_ :: m) (inj-r i) = at-index m i

    HasKey : FinMapRaw K V -> K -> Type ℓK
    HasKey m k = Σ[ i ∈ Index m ] ∥ proj₁ (at-index m i) == k ∥

    lookup : (m : FinMapRaw K V) -> (k : K) -> HasKey m k -> V
    lookup m _ (i , _) = proj₂ (at-index m i)

  MapStructure-FinMap : MapStructure K V (FinMapRaw K V) ℓK
  MapStructure-FinMap .MapStructure.Support = HasKey
  MapStructure-FinMap .MapStructure.lookup = lookup

  UniqueKeys : Pred (FinMapRaw K V) ℓK
  UniqueKeys m = ∀ k -> isProp (HasKey m k)

FinMapUK : {ℓK ℓV : Level} -> Type ℓK -> Type ℓV -> Type (ℓ-max ℓK ℓV)
FinMapUK K V = Σ (FinMapRaw K V) UniqueKeys

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  MapStructure-FinMapUK : MapStructure K V (FinMapUK K V) ℓK
  MapStructure-FinMapUK .MapStructure.Support m =
    MapStructure.Support MapStructure-FinMap (fst m)
  MapStructure-FinMapUK .MapStructure.lookup m =
    MapStructure.lookup MapStructure-FinMap (fst m)


module _ {ℓK ℓV ℓM ℓS : Level} {K : Type ℓK} {V : Type ℓV} {M : Type ℓM}
         (MS : MapStructure K V M ℓS) where
  private
    module MS = MapStructure MS

  MapEq : Rel M (ℓ-max* 3 ℓK ℓV ℓS)
  MapEq l r = (k : K) -> (sl : MS.Support l k) -> (sr : MS.Support r k) ->
              ∥ MS.lookup l k sl == MS.lookup r k sr ∥

  QuotMap : Type _
  QuotMap = M / MapEq


FinMap : {ℓK ℓV : Level} -> Type ℓK -> Type ℓV -> Type (ℓ-max ℓK ℓV)
FinMap K V = QuotMap (MapStructure-FinMapUK {K = K} {V = V})

module _ {ℓK ℓV ℓM ℓS : Level} {K : Type ℓK} {V : Type ℓV} {M : Type ℓM}
         {{MS : MapStructure K V M ℓS}} where
  private
    module MS = MapStructure MS

  map⊆ : M -> M -> Type _
  map⊆ l r = ∀ k -> (sl : MS.Support l k) ->
             ∃[ sr ∈ MS.Support r k ] (MS.lookup l k sl == MS.lookup r k sr)








module _ {ℓK ℓV ℓM ℓS : Level} {K : Type ℓK} {V : Type ℓV} {M : Type ℓM}
         (MS : MapStructure K V M ℓS) where
  private
    module MS = MapStructure MS

    UniqueEntries : Pred M (ℓ-max* 3 ℓK ℓV ℓS)
    UniqueEntries m = isContr (Image (MS.lookup' m))

    M-UK : Type (ℓ-max* 4 ℓM ℓK ℓS ℓV)
    M-UK = Σ M UniqueEntries

  MapStructure-M-UK : MapStructure K V M-UK ℓS
  MapStructure-M-UK .MapStructure.Support m =
    MapStructure.Support MS (fst m)
  MapStructure-M-UK .MapStructure.lookup m =
    MapStructure.lookup MS (fst m)


