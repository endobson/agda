{-# OPTIONS --cubical --safe --exact-split #-}

module int.order where

open import abs
open import base
open import equality
open import hlevel
open import int
open import nat.arithmetic
open import nat.properties
open import relation
open import sigma

import nat.order as n


_≤_ : Int -> Int -> Type₀
i ≤ j = Σ[ x ∈ Nat ] ((int x) + i == j)

_≥_ : Int -> Int -> Type₀
i ≥ j = j ≤ i

isProp-≤ : {i j : Int} -> isProp (i ≤ j)
isProp-≤ {i} (x1 , p1) (x2 , p2) =
  ΣProp-path (isSetInt _ _)
    (nonneg-injective (+-right-injective i (p1 >=> sym p2)))


refl-≤ : Reflexive _≤_
refl-≤ = 0 , +-left-zero

trans-≤ : Transitive _≤_
trans-≤ (x1 , p1) (x2 , p2) =
  (x2 +' x1) , +-left (int-inject-+') >=> +-assoc >=> +-right p1 >=> p2

antisym-≤ : Antisymmetric _≤_
antisym-≤ {i} {j} (x1 , p1) (x2 , p2) = sym p2 >=> +-left (cong int x2-path) >=> +-left-zero
  where
  x2-path : x2 == 0
  x2-path =
    m+'n==0->m==0
      (nonneg-injective
        (int-inject-+' >=>
          (+-right-injective i (+-assoc >=> +-right p1 >=> p2 >=> sym +-left-zero))))


_<_ : Int -> Int -> Type₀
i < j = Σ[ x ∈ Nat⁺ ] ((int ⟨ x ⟩) + i == j)

_>_ : Int -> Int -> Type₀
i > j = j < i

_≮_ : Int -> Int -> Type₀
m ≮ n = ¬ (m < n)

_≯_ : Int -> Int -> Type₀
m ≯ n = ¬ (m > n)


isProp-< : {i j : Int} -> isProp (i < j)
isProp-< {i} (x1 , p1) (x2 , p2) =
  ΣProp-path (isSetInt _ _)
    (ΣProp-path isPropPos' (nonneg-injective (+-right-injective i (p1 >=> sym p2))))

irrefl-< : Irreflexive _<_
irrefl-< {i} (x⁺@(x , pos-x) , p) = subst Pos' x-path pos-x
  where
  x-path : x == 0
  x-path = nonneg-injective (+-right-injective i (p >=> sym +-left-zero))

trans-< : Transitive _<_
trans-< {i} {j} {k} (x1⁺@(x1 , _) , p1) (x2⁺@(x2 , _) , p2) = ((x2⁺ +⁺ x1⁺) , path2)
  where
  path2 : (int (x2 +' x1)) + i == k
  path2 = snd (trans-≤ (x1 , p1) (x2 , p2))

asym-< : Asymmetric _<_
asym-< {i} {j} (x1⁺@(x1 , _) , p1) (x2⁺@(x2 , _) , p2) = irrefl-< ((x2⁺ +⁺ x1⁺) , path2)
  where
  path2 : (int (x2 +' x1)) + i == i
  path2 = snd (trans-≤ (x1 , p1) (x2 , p2))


-- Utilities for combining the orders

trans-<-≤ : {i j k : Int} -> (i < j) -> (j ≤ k) -> (i < k)
trans-<-≤ ((x , x-pos) , x-path) (y , y-path) =
  ((y +' x) , +'-Pos-right x-pos) , +-left int-inject-+' >=> +-assoc >=> +-right x-path >=> y-path

trans-≤-< : {i j k : Int} -> (i ≤ j) -> (j < k) -> (i < k)
trans-≤-< (x , x-path) ((y , y-pos) , y-path) =
  ((y +' x) , +'-Pos-left y-pos) , +-left int-inject-+' >=> +-assoc >=> +-right x-path >=> y-path

weaken-< : {i j : Int} -> i < j -> i ≤ j
weaken-< ((x , _) , p) = (x , p)

-- Computing the order for new values

split-< : HeteroConnex _<_ _≤_
split-< i j =
  handle (i + (- j)) (+-assoc >=> +-right (+-commute >=> add-minus-zero) >=> +-right-zero)
  where
  handle : (k : Int) -> k + j == i -> (i < j) ⊎ (j ≤ i)
  handle (nonneg k) p = inj-r (k , p)
  handle (neg k) p = inj-l ((suc k , tt) , sym path)
    where
    path : j == (pos k) + i
    path = sym +-left-zero >=> +-left (sym add-minus-zero) >=> +-assoc >=> cong ((pos k) +_) p

comparison-< : {i j : Int} -> (i < j) -> (k : Int) ->  (i < k) ⊎ (k < j)
comparison-< {i} {j} i<j k =
  case (split-< i k) of (\
    { (inj-l i<k) -> (inj-l i<k)
    ; (inj-r k≤i) -> (inj-r (trans-≤-< k≤i i<j))
    })

connex-≤ : Connex _≤_
connex-≤ i j =
  case (split-< i j) of (\
    { (inj-l i<j) -> (inj-l (weaken-< i<j))
    ; (inj-r j≤i) -> (inj-r j≤i)
    })

connected-< : Connected _<_
connected-< {i} {j} i≮j j≮i =
  case (split-< i j) of (\
    { (inj-l i<j) -> bot-elim (i≮j i<j)
    ; (inj-r j≤i) ->
      case (split-< j i) of (\
        { (inj-l j<i) -> bot-elim (j≮i j<i)
        ; (inj-r i≤j) -> antisym-≤ i≤j j≤i
        })
    })

-- Preserved by basic operations

+₁-preserves-≤ : {a b : Int} -> (c : Int) -> a ≤ b -> (c + a) ≤ (c + b)
+₁-preserves-≤ {a} {b} c (x , p) = x , sym +-assoc >=> +-left +-commute >=> +-assoc >=> cong (c +_) p

+₂-preserves-≤ : {a b : Int} -> (c : Int) -> a ≤ b -> (a + c) ≤ (b + c)
+₂-preserves-≤ {a} {b} c (x , p) = x , sym +-assoc >=> (cong (_+ c) p)

+₁-preserves-< : {a b : Int} -> (c : Int) -> a < b -> (c + a) < (c + b)
+₁-preserves-< {a} {b} c (x , p) = x , sym +-assoc >=> +-left +-commute >=> +-assoc >=> cong (c +_) p

+₂-preserves-< : {a b : Int} -> (c : Int) -> a < b -> (a + c) < (b + c)
+₂-preserves-< {a} {b} c (x , p) = x , sym +-assoc >=> (cong (_+ c) p)
