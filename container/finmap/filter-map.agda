{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

open import base
open import container.finmap
open import equality
open import maybe

module container.finmap.filter-map where

module _ {ℓK : Level} {ℓV : Level} {K : Type ℓK} {V : Type ℓV} where


  module _ {ℓK2 ℓV2 : Level} {K2 : Type ℓK2} {V2 : Type ℓV2} (f : K -> V -> Maybe (K2 × V2)) where

    private
      maybe-cons : Maybe (K2 × V2) -> FinMap' K2 V2 -> FinMap' K2 V2
      maybe-cons (just (k2 , v2)) m = fm-cons k2 v2 m
      maybe-cons (nothing) m = m

      HasKey-maybe-cons : {k : K2} {v : V2} {b : Maybe (K2 × V2)} {m : FinMap' K2 V2} -> 
                          HasKV' k v m -> HasKV' k v (maybe-cons b m)
      HasKey-maybe-cons {b = just (k , v)} hk = has-kv-skip k v hk
      HasKey-maybe-cons {b = nothing} hk = hk

      filtered-cons : K -> V -> FinMap' K2 V2 -> FinMap' K2 V2
      filtered-cons k v m = maybe-cons (f k v) m

      filtered-cons-keep : {k : K} {v : V} {k2 : K2} {v2 : V2} {m : FinMap' K2 V2} -> 
        (f k v) == just (k2 , v2) -> filtered-cons k v m == fm-cons k2 v2 m
      filtered-cons-keep p = cong (\x -> maybe-cons x _) p

      filtered-cons-drop : {k : K} {v : V} {m : FinMap' K2 V2} -> 
        (f k v) == nothing -> filtered-cons k v m == m
      filtered-cons-drop p = cong (\x -> maybe-cons x _) p


    finmap'-filter-map : FinMap' K V -> FinMap' K2 V2
    finmap'-filter-map [] = [] 
    finmap'-filter-map (fm-cons k v m) = filtered-cons k v (finmap'-filter-map m)

    HasKey-finmap'-filter-map :
      {k2 : K2} {v2 : V2} {m : FinMap' K V} -> 
      Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m × (f k v) == just (k2 , v2)) -> 
      HasKV' k2 v2 (finmap'-filter-map m)
    HasKey-finmap'-filter-map
      {k2} {v2} {m = m@(fm-cons k4 v4 m')} 
      (k , v , (has-kv-here kp vp _)  , fp) = ans
      where

      ans : HasKV' k2 v2 (finmap'-filter-map (fm-cons k4 v4 m'))
      ans = subst (HasKV' k2 v2) (sym (filtered-cons-keep fp) >=> 
                                  cong2 (\k v -> finmap'-filter-map (fm-cons k v m')) kp vp) 
                                 (has-kv-here refl refl _)

    HasKey-finmap'-filter-map (k , v , (has-kv-skip k3 v3 hk) , fp) = 
      HasKey-maybe-cons (HasKey-finmap'-filter-map (k , v , hk , fp))


    HasKey-finmap'-filter-map-backward :
      {k2 : K2} {v2 : V2} {m : FinMap' K V} -> 
      HasKV' k2 v2 (finmap'-filter-map m) -> 
      Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m × (f k v) == just (k2 , v2))
    HasKey-finmap'-filter-map-backward {k2} {v2} m@{fm-cons k v m'} hkv =
      handle (f k v) refl
      where
      Ans : FinMap' K V -> Type _
      Ans m = Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m × (f k v) == just (k2 , v2))
      handle : (b : Maybe (K2 × V2)) -> f k v == b -> Ans m
      handle (nothing) p = 
        case (HasKey-finmap'-filter-map-backward hkv') of (\{
          (k , v , hkv , p) -> (k , v , has-kv-skip _ _ hkv , p) })
        where
        hkv' : HasKV' k2 v2 (finmap'-filter-map m')
        hkv' = subst (HasKV' k2 v2) (filtered-cons-drop p) hkv
      handle (just (k3 , v3)) p = handle2 hkv' -- (k , v , has-kv-here refl refl m' , ?)
        where
        hkv' : HasKV' k2 v2 (fm-cons k3 v3 (finmap'-filter-map m'))
        hkv' = subst (HasKV' k2 v2) (filtered-cons-keep p) hkv
        handle2 : HasKV' k2 v2 (fm-cons k3 v3 (finmap'-filter-map m')) -> Ans m
        handle2 (has-kv-here kp vp _) = 
          (k , v , has-kv-here refl refl m' , p >=> (\i -> just (kp (~ i) , vp (~ i))))
        handle2 (has-kv-skip _ _ hkv) =
          case (HasKey-finmap'-filter-map-backward hkv) of (\{
            (k , v , hkv , p) -> (k , v , has-kv-skip _ _ hkv , p) })

