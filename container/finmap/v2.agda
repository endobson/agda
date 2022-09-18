{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.v2 where

open import base
open import finset
open import hlevel
open import equality-path
open import functions
open import functions.embedding
open import equivalence
open import relation
open import cubical

private
  variable
    ℓ ℓA ℓB ℓC ℓK ℓV : Level
    A B C K V : Type ℓ


record Map (K : Type ℓK) (V : Type ℓV) (ℓ : Level) 
  : Type (ℓ-max* 3 ℓK ℓV (ℓ-suc ℓ)) where
  field
    Index : Type ℓ
    keyAt : Index ↪ K
    valueAt : Index -> V

Map-compose : Map A B ℓ -> Map B C ℓ -> Map A C (ℓ-max ℓ (levelOf B))
Map-compose {A = A} {B = B} {C = C} m1 m2 = record
  { Index = Index
  ; keyAt = keyAt
  ; valueAt = valueAt
  }
  where
  module m1 = Map m1
  module m2 = Map m2

  Index : Type _
  Index = Σ[ j1 ∈ m1.Index ] Σ[ j2 ∈ m2.Index ] (⟨ m2.keyAt ⟩ j2 == m1.valueAt j1)

  keyAt' : Index -> A
  keyAt' (j1 , j2 , p) = ⟨ m1.keyAt ⟩ j1

  keyAt : Index ↪ A
  keyAt = keyAt' , eqInv isEmbedding-eq-hasPropFibers pfibers
    where
    pfibers' : ∀ (a : A) -> isProp (fiber ⟨ m1.keyAt ⟩ a)
    pfibers' = eqFun isEmbedding-eq-hasPropFibers (snd m1.keyAt)

    pfibers : ∀ (a : A) -> isProp (fiber keyAt' a)
    pfibers a ((j11 , j21 , p1) , q1) ((j12 , j22 , p2) , q2) = 
      (\i -> ((j1-path i , j2-path i , p-path i) , q-path i))
      where
      check : (j11 , q1) == (j12 , q2)
      check = pfibers' a (j11 , q1) (j12 , q2)

      j1-path : j11 == j12
      j1-path = cong fst check

      q-path : PathP (\i -> ⟨ m1.keyAt ⟩ (j1-path i) == a) q1 q2
      q-path = cong snd check

      check2 : ⟨ m2.keyAt ⟩ j21 == ⟨ m2.keyAt ⟩ j22
      check2 = p1 ∙∙ (cong m1.valueAt j1-path) ∙∙ sym p2

      j2-path : j21 == j22
      j2-path = isEqInv (snd m2.keyAt j21 j22) check2

      j2-path-rev : ⟨ m2.keyAt ⟩ j21 == ⟨ m2.keyAt ⟩ j22
      j2-path-rev = isEqFun (snd m2.keyAt j21 j22) j2-path

      c-j2-path-rev : j2-path-rev == check2
      c-j2-path-rev = isEqSec (snd m2.keyAt j21 j22) check2

      p-path'2 : Square p1 p2 check2 (cong m1.valueAt (j1-path))
      p-path'2 i j = square-filler (sym p1) (sym p2) (cong m1.valueAt (j1-path)) i (~ j)

      p-path' : Square p1 p2 j2-path-rev (cong m1.valueAt (j1-path))
      p-path' = subst (\P -> Square p1 p2 P (cong m1.valueAt (j1-path))) (sym c-j2-path-rev) p-path'2

      p-path : PathP (\i -> ⟨ m2.keyAt ⟩ (j2-path i) == m1.valueAt (j1-path i)) p1 p2
      p-path = p-path'

  valueAt : Index -> C
  valueAt (_ , j2 , _) = m2.valueAt j2

identity-Map : Map A A (levelOf A)
identity-Map {A = A} = record
  { Index = A
  ; keyAt = (\a -> a) , (\ _ _ -> idIsEquiv _)
  ; valueAt = (\a -> a)
  }

isFinMap : Pred (Map K V ℓ) ℓ
isFinMap m = isFinSet (Map.Index m)

FinMap : (K : Type ℓK) (V : Type ℓV) (ℓ : Level) -> Type (ℓ-max* 3 ℓK ℓV (ℓ-suc ℓ))
FinMap K V ℓ = Σ (Map K V ℓ) isFinMap

-- FinMap-compose : 

FinMap-compose : FinMap A B ℓ -> FinMap B C ℓ -> FinMap A C (ℓ-max ℓ (levelOf B))
FinMap-compose _ = ?


