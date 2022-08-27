{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.trunc-path where

open import base
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

FinMap : {ℓK ℓV : Level} -> Type ℓK -> Type ℓV -> Type (ℓ-max ℓK ℓV)
FinMap K V = List (K × V)

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  private
    Index : FinMap K V -> Type₀
    Index m = FinT (length m)

    at-index : (m : FinMap K V) -> Index m -> K × V
    at-index (e :: _) (inj-l _) = e
    at-index (_ :: m) (inj-r i) = at-index m i

    HasKey : FinMap K V -> K -> Type ℓK
    HasKey m k = Σ[ i ∈ Index m ] ∥ proj₁ (at-index m i) == k ∥

    lookup : (m : FinMap K V) -> (k : K) -> HasKey m k -> V
    lookup m _ (i , _) = proj₂ (at-index m i)

  MapStructure-FinMap : MapStructure K V (FinMap K V) ℓK
  MapStructure-FinMap .MapStructure.Support = HasKey
  MapStructure-FinMap .MapStructure.lookup = lookup

  UniqueKeys : Pred (FinMap K V) ℓK
  UniqueKeys m = ∀ k -> isProp (HasKey m k)

FinMapUK : {ℓK ℓV : Level} -> Type ℓK -> Type ℓV -> Type (ℓ-max ℓK ℓV)
FinMapUK K V = Σ (FinMap K V) UniqueKeys

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
  

