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
    ; isLinearOrder-< = record
      { isProp-< = o.isProp-<
      ; irrefl-< = o.irrefl-<
      ; trans-< = o.trans-<
      ; connected-< = connected-S<
      ; comparison-< = comparison-S<
      }
    }
    where
    module o = LinearOrderStr o

    S< : Rel (∈-Subtype S) _
    S< (x , _) (y , _) = x o.< y

    connected-S< : Connected S<
    connected-S< x≮y y≮x = ΣProp-path (\{x} -> snd (S x)) (o.connected-< x≮y y≮x)

    comparison-S< : Comparison S<
    comparison-S< (x , sx) (y , sy) (z , sz) x<z = (o.comparison-< x y z x<z)


  module _ {ℓ≤ : Level} {A≤ : Rel A ℓ≤} (PO : isPartialOrder A≤) where
    private
      instance
        IPO = PO
      S≤ : Rel (∈-Subtype S) _
      S≤ (x , _) (y , _) = x ≤ y

    isPartialOrder->isPartialOrder-Subtype≤ : isPartialOrder S≤
    isPartialOrder->isPartialOrder-Subtype≤ = record
      { isProp-≤ = isProp-≤
      ; refl-≤ = refl-≤
      ; trans-≤ = trans-≤
      ; antisym-≤ = antisym-S≤
      }
      where
      antisym-S≤ : Antisymmetric S≤
      antisym-S≤ x≤y y≤x = ΣProp-path (\{x} -> snd (S x)) (antisym-≤ x≤y y≤x)

  TotalOrderStr-Subtype :
    {ℓ≤ : Level} {A≤ : Rel A ℓ≤} {PO : isPartialOrder A≤} ->
    (TotalOrderStr PO) -> TotalOrderStr (isPartialOrder->isPartialOrder-Subtype≤ PO)
  TotalOrderStr-Subtype o = record { connex-≤ = \(x , _) (y , _) -> o.connex-≤ x y }
    where
    module o = TotalOrderStr o
