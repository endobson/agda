{-# OPTIONS --cubical --safe --exact-split #-}

module order.subtype where

open import base
open import order
open import relation
open import subset
open import truncation
open import sigma.base
open import sum

module _ {ℓA ℓS : Level} {A : Type ℓA} (S : Subtype A ℓS) where
  LinearOrderStr-Subtype : {ℓ< : Level} -> LinearOrderStr A ℓ< -> LinearOrderStr (∈-Subtype S) ℓ<
  LinearOrderStr-Subtype o = record
    { _<_ = S<
    ; isProp-< = o.isProp-<
    ; irrefl-< = o.irrefl-<
    ; trans-< = o.trans-<
    ; connected-< = connected-S<
    ; comparison-< = comparison-S<
    }
    where
    module o = LinearOrderStr o

    S< : Rel (∈-Subtype S) _
    S< (x , _) (y , _) = x o.< y

    connected-S< : Connected S<
    connected-S< x≮y y≮x = ΣProp-path (\{x} -> snd (S x)) (o.connected-< x≮y y≮x)

    comparison-S< : Comparison S<
    comparison-S< (x , sx) (y , sy) (z , sz) x<z = (o.comparison-< x y z x<z)

  PartialOrderStr-Subtype : {ℓ≤ : Level} -> PartialOrderStr A ℓ≤ -> PartialOrderStr (∈-Subtype S) ℓ≤
  PartialOrderStr-Subtype o = record
    { _≤_ = S≤
    ; isProp-≤ = o.isProp-≤
    ; refl-≤ = o.refl-≤
    ; trans-≤ = o.trans-≤
    ; antisym-≤ = antisym-S≤
    }
    where
    module o = PartialOrderStr o

    S≤ : Rel (∈-Subtype S) _
    S≤ (x , _) (y , _) = x o.≤ y

    antisym-S≤ : Antisymmetric S≤
    antisym-S≤ x≤y y≤x = ΣProp-path (\{x} -> snd (S x)) (o.antisym-≤ x≤y y≤x)

  TotalOrderStr-Subtype :
    {ℓ≤ : Level} {PO : PartialOrderStr A ℓ≤} ->
    (TotalOrderStr PO) -> TotalOrderStr (PartialOrderStr-Subtype PO)
  TotalOrderStr-Subtype o = record { connex-≤ = \(x , _) (y , _) -> o.connex-≤ x y }
    where
    module o = TotalOrderStr o
