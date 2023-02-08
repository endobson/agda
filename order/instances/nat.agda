{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.nat where

open import base

open import additive-group
open import additive-group.instances.nat
open import equality
open import functions
open import nat
open import nat.order.base
open import order
open import relation
open import sum
open import truncation
open import truncation


private

  irrefl-ℕ< : {n : Nat} -> ¬(n ℕ< n)
  irrefl-ℕ< {zero} (i , p) = zero-suc-absurd (sym p >=> +'-right-suc)
  irrefl-ℕ< {suc n} lt = irrefl-ℕ< (pred-≤ lt)

  antisym-ℕ≤ : {m n : Nat} -> m ℕ≤ n -> n ℕ≤ m -> m == n
  antisym-ℕ≤ (zero  , p1) _ = p1
  antisym-ℕ≤ {m} {n} (suc i , p1) (j , p2) = bot-elim (irrefl-ℕ< n<n)
    where
    ap : (i + j) + (suc n) == n
    ap = +'-right-suc >=> (+-assocᵉ (suc i) j n >=> cong (suc i +_) p2 >=> p1)

    n<n : n ℕ< n
    n<n = (i + j) , ap

  trans-ℕ≤ : {m n o : Nat} -> m ℕ≤ n -> n ℕ≤ o -> m ℕ≤ o
  trans-ℕ≤ {m} (x1 , p1) (x2 , p2) =
    x2 + x1 ,
    +-assocᵉ x2 x1 _ >=>
    cong (x2 +_) p1 >=>
    p2

  trans-ℕ≤-ℕ< : {m n o : Nat} -> m ℕ≤ n -> n ℕ< o -> m ℕ< o
  trans-ℕ≤-ℕ< lt1 lt2 = trans-ℕ≤ (suc-≤ lt1) lt2

  weaken-ℕ< : {m n : Nat} -> m ℕ< n -> m ℕ≤ n
  weaken-ℕ< lt = pred-≤ (right-suc-≤ lt)

  trans-ℕ< : {m n o : Nat} -> (m ℕ< n) -> (n ℕ< o) -> (m ℕ< o)
  trans-ℕ< lt1 lt2 = trans-ℕ≤-ℕ< (weaken-ℕ< lt1) lt2


  split-ℕ< : (x : Nat) -> (y : Nat) -> (x ℕ< y) ⊎ (y ℕ≤ x)
  split-ℕ< _       zero    = inj-r zero-≤
  split-ℕ< zero    (suc n) = inj-l zero-<
  split-ℕ< (suc m) (suc n) with (split-ℕ< m n)
  ... | inj-l lt = inj-l (suc-≤ lt)
  ... | inj-r lt = inj-r (suc-≤ lt)

  convert-ℕ≮ : {m n : Nat} -> ¬ (m ℕ< n) -> n ℕ≤ m
  convert-ℕ≮ = proj-¬l (split-ℕ< _ _)

  connected-ℕ< : Connected _ℕ<_
  connected-ℕ< x≮y y≮x =
    antisym-ℕ≤ (proj-¬l (split-ℕ< _ _) y≮x) (proj-¬l (split-ℕ< _ _) x≮y)

  comparison-ℕ< : Comparison _ℕ<_
  comparison-ℕ< x y z x<z = handle (split-ℕ< x y)
    where
    handle : (x ℕ< y) ⊎ (y ℕ≤ x) -> ∥ (x ℕ< y) ⊎ (y ℕ< z) ∥
    handle (inj-l x<y) = ∣ inj-l x<y ∣
    handle (inj-r y≤x) = ∣ inj-r (trans-ℕ≤-ℕ< y≤x x<z) ∣

instance
  LinearOrderStr-ℕ : LinearOrderStr Nat ℓ-zero
  LinearOrderStr-ℕ = record
    { _<_ = _ℕ<_
    ; isLinearOrder-< = record
      { isProp-< = isProp-ℕ≤
      ; irrefl-< = irrefl-ℕ<
      ; trans-< = trans-ℕ<
      ; connected-< = connected-ℕ<
      ; comparison-< = comparison-ℕ<
      }
    }

private
  refl-ℕ≤ : {n : Nat} -> n ℕ≤ n
  refl-ℕ≤ {zero} = zero-≤
  refl-ℕ≤ {suc n} = suc-≤ refl-ℕ≤

instance
  PartialOrderStr-ℕ : PartialOrderStr Nat ℓ-zero
  PartialOrderStr-ℕ = record
    { _≤_ = _ℕ≤_
    ; isPartialOrder-≤ = record
      { isProp-≤ = isProp-ℕ≤
      ; refl-≤ = refl-ℕ≤
      ; trans-≤ = trans-ℕ≤
      ; antisym-≤ = antisym-ℕ≤
      }
    }

instance
  CompatibleOrderStr-ℕ :
    CompatibleOrderStr LinearOrderStr-ℕ PartialOrderStr-ℕ
  CompatibleOrderStr-ℕ = record
    { convert-≮ = convert-ℕ≮
    }

private
  trichotomous-ℕ< : Trichotomous _<_
  trichotomous-ℕ< x y = handle (split-ℕ< x y) (split-ℕ< y x)
    where
    handle : (x < y ⊎ y ≤ x) -> (y < x ⊎ x ≤ y) -> Tri< x y
    handle (inj-l x<y) _            = tri<' x<y
    handle (inj-r y≤x) (inj-l y<x) = tri>' y<x
    handle (inj-r y≤x) (inj-r x≤y) = tri=' (antisym-≤ x≤y y≤x)

instance
  DecidableLinearOrderStr-ℕ : DecidableLinearOrderStr LinearOrderStr-ℕ
  DecidableLinearOrderStr-ℕ = record
    { trichotomous-< = trichotomous-ℕ<
    }
  TotalOrderStr-ℕ : TotalOrderStr PartialOrderStr-ℕ
  TotalOrderStr-ℕ = TotalOrderStr-LinearOrder
