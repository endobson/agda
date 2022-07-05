{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import container.finmap
open import container.finmap.filter-map
open import equality
open import functions
open import maybe

module container.finmap.entry-map where

module _ {ℓK : Level} {ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  module _ {ℓK2 ℓV2 : Level} {K2 : Type ℓK2} {V2 : Type ℓV2} (f : K -> V -> (K2 × V2)) where

    private
      f' : K -> V -> Maybe (K2 × V2)
      f' = (\k v -> just (f k v))

    finmap'-entry-map : FinMap' K V -> FinMap' K2 V2
    finmap'-entry-map = finmap'-filter-map f'

    HasKey-finmap'-entry-map :
      {k : K} {v : V} {m : FinMap' K V} -> 
      HasKV' k v m  -> 
      HasKV' (fst (f k v)) (snd (f k v)) (finmap'-entry-map m)
    HasKey-finmap'-entry-map hkv = HasKey-finmap'-filter-map f' (_ , _ , hkv , refl)


    HasKey-finmap'-entry-map-backward :
      {k2 : K2} {v2 : V2} {m : FinMap' K V} -> 
      HasKV' k2 v2 (finmap'-entry-map m) -> 
      Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m × (f k v) == (k2 , v2))
    HasKey-finmap'-entry-map-backward hkv = 
      case (HasKey-finmap'-filter-map-backward f' hkv) of 
        (\{ (k , v , hkv , p) -> k , v , hkv , just-injective p})

