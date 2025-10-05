{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.int where

open import abs
open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality-path
open import hlevel.base
open import int
open import nat.arithmetic
open import nat.properties
open import order
open import relation
open import sigma.base
open import truncation

private
  _ℤ≤_ : Int -> Int -> Type₀
  i ℤ≤ j = Σ[ x ∈ Nat ] ((int x) + i == j)

  isProp-ℤ≤ : {i j : Int} -> isProp (i ℤ≤ j)
  isProp-ℤ≤ {i} (x1 , p1) (x2 , p2) =
    ΣProp-path (isSetInt _ _)
      (nonneg-injective (+-right-injective i (p1 >=> sym p2)))


  refl-ℤ≤ : Reflexive _ℤ≤_
  refl-ℤ≤ = 0 , +-left-zero

  trans-ℤ≤ : Transitive _ℤ≤_
  trans-ℤ≤ (x1 , p1) (x2 , p2) =
    (x2 + x1) , +-left (int-inject-+') >=> +-assoc >=> +-right p1 >=> p2

  antisym-ℤ≤ : Antisymmetric _ℤ≤_
  antisym-ℤ≤ {i} {j} (x1 , p1) (x2 , p2) = sym p2 >=> +-left (cong int x2-path) >=> +-left-zero
    where
    x2-path : x2 == 0
    x2-path =
      m+'n==0->m==0
        (nonneg-injective
          (int-inject-+' >=>
            (+-right-injective i (+-assoc >=> +-right p1 >=> p2 >=> sym +-left-zero))))


  _ℤ<_ : Int -> Int -> Type₀
  i ℤ< j = Σ[ x ∈ Nat⁺ ] ((int ⟨ x ⟩) + i == j)

  isProp-ℤ< : {i j : Int} -> isProp (i ℤ< j)
  isProp-ℤ< {i} (x1 , p1) (x2 , p2) =
    ΣProp-path (isSetInt _ _)
      (ΣProp-path isPropPos' (nonneg-injective (+-right-injective i (p1 >=> sym p2))))

  irrefl-ℤ< : Irreflexive _ℤ<_
  irrefl-ℤ< {i} (x⁺@(x , pos-x) , p) = subst Pos' x-path pos-x
    where
    x-path : x == 0
    x-path = nonneg-injective (+-right-injective i (p >=> sym +-left-zero))

  trans-ℤ< : Transitive _ℤ<_
  trans-ℤ< {i} {j} {k} (x1⁺@(x1 , _) , p1) (x2⁺@(x2 , _) , p2) = ((x2⁺ +⁺ x1⁺) , path2)
    where
    path2 : (int (x2 + x1)) + i == k
    path2 = snd (trans-ℤ≤ (x1 , p1) (x2 , p2))

  asym-ℤ< : Asymmetric _ℤ<_
  asym-ℤ< lt1 lt2 = irrefl-ℤ< (trans-ℤ< lt1 lt2)


  -- Utilities for combining the orders
  trans-ℤ≤-ℤ< : {i j k : Int} -> (i ℤ≤ j) -> (j ℤ< k) -> (i ℤ< k)
  trans-ℤ≤-ℤ< (x , x-path) ((y , y-pos) , y-path) =
    ((y + x) , +'-Pos-left y-pos) , +-left int-inject-+' >=> +-assoc >=> +-right x-path >=> y-path

  weaken-ℤ< : {i j : Int} -> i ℤ< j -> i ℤ≤ j
  weaken-ℤ< ((x , _) , p) = (x , p)

  -- Computing the order for new values

  split-ℤ< : HeteroConnex' _ℤ<_ _ℤ≤_
  split-ℤ< i j =
    handle (i + (- j)) (+-assoc >=> +-right (+-commute >=> add-minus-zero) >=> +-right-zero)
    where
    handle : (k : Int) -> k + j == i -> (i ℤ< j) ⊎ (j ℤ≤ i)
    handle (nonneg k) p = inj-r (k , p)
    handle (neg k) p = inj-l ((suc k , tt) , sym path)
      where
      path : j == (pos k) + i
      path = sym +-left-zero >=> +-left (sym add-minus-zero) >=> +-assoc >=> cong ((pos k) +_) p

  comparison-ℤ< : {i j : Int} -> (i ℤ< j) -> (k : Int) ->  (i ℤ< k) ⊎ (k ℤ< j)
  comparison-ℤ< {i} {j} i<j k =
    case (split-ℤ< i k) of (\
      { (inj-l i<k) -> (inj-l i<k)
      ; (inj-r k≤i) -> (inj-r (trans-ℤ≤-ℤ< k≤i i<j))
      })

  connex-ℤ≤ : Connex _ℤ≤_
  connex-ℤ≤ i j =
    ∣ case (split-ℤ< i j) of (\
        { (inj-l i<j) -> (inj-l (weaken-ℤ< i<j))
        ; (inj-r j≤i) -> (inj-r j≤i)
        }) ∣

  connected-ℤ< : Connected _ℤ<_
  connected-ℤ< {i} {j} i≮j j≮i =
    case (split-ℤ< i j) of (\
      { (inj-l i<j) -> bot-elim (i≮j i<j)
      ; (inj-r j≤i) ->
        case (split-ℤ< j i) of (\
          { (inj-l j<i) -> bot-elim (j≮i j<i)
          ; (inj-r i≤j) -> antisym-ℤ≤ i≤j j≤i
          })
      })

instance
  isLinearOrder-ℤ< : isLinearOrder _ℤ<_
  isLinearOrder-ℤ< = record
    { isProp-< = isProp-ℤ<
    ; irrefl-< = irrefl-ℤ<
    ; trans-< = trans-ℤ<
    ; connected-< = connected-ℤ<
    ; comparison-< = \i j k i<k -> ∣ comparison-ℤ< i<k j ∣
    }

  isPartialOrder-ℤ≤ : isPartialOrder _ℤ≤_
  isPartialOrder-ℤ≤ = record
    { isProp-≤ = isProp-ℤ≤
    ; refl-≤ = refl-ℤ≤
    ; trans-≤ = trans-ℤ≤
    ; antisym-≤ = antisym-ℤ≤
    }

private
  trichotomous-ℤ< : Trichotomous _ℤ<_
  trichotomous-ℤ< i j = handle (split-ℤ< i j) (split-ℤ< j i)
    where
    handle : (i < j ⊎ j ≤ i) -> (j < i ⊎ i ≤ j) -> Tri (i < j) (i == j) (j < i)
    handle (inj-l i<j) _           = tri<' i<j
    handle (inj-r j≤i) (inj-l j<i) = tri>' j<i
    handle (inj-r j≤i) (inj-r i≤j) = tri=' (antisym-≤ i≤j j≤i)

instance
  DecidableLinearOrderStr-ℤ : DecidableLinearOrderStr useⁱ
  DecidableLinearOrderStr-ℤ = record
    { trichotomous-< = trichotomous-ℤ<
    }


private
  convert-ℤ≮ : {m n : ℤ} -> ¬ (m < n) -> n ≤ m
  convert-ℤ≮ {m} {n} m≮n = case (trichotomous-< m n) of
    \{ (tri< m<n _ _) -> bot-elim (m≮n m<n)
     ; (tri= _ m=n _) -> path-≤ (sym m=n)
     ; (tri> _ _ m>n) -> weaken-ℤ< m>n
     }

instance
  CompatibleOrderStr-ℤ : CompatibleOrderStr useⁱ useⁱ
  CompatibleOrderStr-ℤ = record
    { convert-≮ = convert-ℤ≮
    }
