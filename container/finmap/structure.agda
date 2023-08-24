{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.structure where

open import base
open import container.finmap hiding (lookup)
open import container.finmap.all-entries
open import finset
open import hlevel
open import relation
open import sigma.base
open import set-quotient
open import truncation


--record MapStructure {ℓK ℓV ℓM : Level}
--       (K : Type ℓK) (V : Type ℓV) (M : Type ℓM) (ℓS : Level) :
--       Type (ℓ-max (ℓ-max* 3 ℓK ℓV ℓM) (ℓ-suc ℓS)) where
--  field
--    Support : M -> K -> Type ℓS
--    lookup : (m : M) -> (k : K) -> Support m k -> V
--
--
--record FinMapStructure {ℓK ℓV ℓM : Level}
--       (K : Type ℓK) (V : Type ℓV) (M : Type ℓM) (ℓS : Level) :
--       Type (ℓ-max (ℓ-max* 3 ℓK ℓV ℓM) (ℓ-suc ℓS)) where
--  field
--    Support : M -> K -> hProp ℓS
--  private
--    S : M -> K -> Type ℓS
--    S m k = ⟨ Support m k ⟩
--
--  field
--    lookup : (m : M) -> (k : K) -> S m k -> V
--    finite-support : (m : M) -> isFinSet (Σ[ k ∈ K ] S m k)
--
--
--
--module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV}
--         {{disc'K : Discrete' K}}
--         {{isSet'V : isSet' V}}
--         where
--  private
--    module FMS = FinMapStructure
--    ℓKV : Level
--    ℓKV = ℓ-max ℓK ℓV
--
--  instance
--    FinMapStructure-FinMapUK : FinMapStructure K V (FinMapUK K V) ℓKV
--    FinMapStructure-FinMapUK .FMS.Support m k =
--      HasKey-UK k m , isProp-HasKey-UK m
--    FinMapStructure-FinMapUK .FMS.lookup m k (v , _) = v
--    FinMapStructure-FinMapUK .FMS.finite-support (m' , _) =
--      isFinSet-AllEntries m'
--
--
--    FinMapStructure-FinMap : FinMapStructure K V (FinMap K V) ℓKV
--    FinMapStructure-FinMap .FMS.Support m k = HasKey-hProp k m
--    FinMapStructure-FinMap .FMS.lookup m k (v , _) = v
--    FinMapStructure-FinMap .FMS.finite-support =
--      FinMapElim.elimProp (\_ -> isProp-isFinSet) isFinSet-entries
--      where
--      module FinMapElim = SetQuotientElim (FinMapUK K V) FinMapEq
--      isFinSet-entries : (m : FinMapUK K V) ->
--        isFinSet (Σ[ k ∈ K ] (Σ[ v ∈ V ] (∥ HasKV-UK k v m ∥)))
--      isFinSet-entries = ?
