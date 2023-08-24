{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.v4.inverse where

open import base
open import container.finmap.v4
open import relation
open import hlevel
open import functions
open import sigma.base

private
  variable
    ℓ ℓK ℓV : Level
    K V : Type ℓ

module _ {K : Type ℓK} {V : Type ℓV}
         {{disc'K : Discrete' K}}
         {{disc'V : Discrete' V}}
         {{isSet'K : isSet' K}}
         {{isSet'V : isSet' V}}
         where
  private
    disc-K : Discrete K
    disc-K = Discrete'.f disc'K

    disc-V : Discrete V
    disc-V = Discrete'.f disc'V

    isSet-K : isSet K
    isSet-K = isSet'.f isSet'K

    isSet-V : isSet V
    isSet-V = isSet'.f isSet'V

  InverseFinMaps : FinMap K V -> FinMap V K -> Type _
  InverseFinMaps m1 m2 = ∀ k v -> (FinMap-HasKV m1 k v) <-> (FinMap-HasKV m2 v k)

  isInvertibleFinMap : Pred (FinMap K V) _
  isInvertibleFinMap m = Σ[ m2 ∈ FinMap V K ] (InverseFinMaps m m2)

--  isProp-isInvertibleFinMap : (m : FinMap K V) -> isProp (isInvertibleFinMap m)
--  isProp-isInvertibleFinMap m (m2 , m-m2) (m3 , m-m3) =
--    ΣProp-path (\{m'} -> isPropΠ2 (\k v -> isProp× (isPropΠ (\_ -> isProp-FinMap-HasKV m' v k))
--                                                   (isPropΠ (\_ -> isProp-FinMap-HasKV m k v))))
--      ?
--    where
--    m2-m3 : ∀ k v -> (FinMap-HasKV m2 v k) <-> (FinMap-HasKV m3 v k)
--    m2-m3 k v = proj₁ (m-m3 k v) ∘ proj₂ (m-m2 k v) ,
--                proj₁ (m-m2 k v) ∘ proj₂ (m-m3 k v)
