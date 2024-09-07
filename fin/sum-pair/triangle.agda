{-# OPTIONS --cubical --safe --exact-split #-}

module fin.sum-pair.triangle where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import fin
open import fin.sum-pair
open import hlevel
open import isomorphism
open import nat
open import order
open import order.instances.nat
open import sigma.base

-- Proof that if there is a triangular amount of indices
-- that indexing by columns or diagonals is the same.

module _ {n : Nat}  where
  private
    forward : Σ[ (k , _) ∈ Fin n ] (FinPair+ k) ->
              Σ[ (fin-pair+ i n-i _) ∈ (FinPair+ n)] (Fin n-i)
    forward ((k , (m , m+sk=n)) , (fin-pair+ i j i+j=k)) =
      (fin-pair+ i (suc j + m) i+j+sm=n) , (j , m , +-commuteᵉ m (suc j))
      where
      i+j+sm=n : i + (suc j + m) == n
      i+j+sm=n =
        sym (+-assocᵉ i (suc j) m) >=>
        +-left (+'-right-suc >=> cong suc i+j=k) >=>
        +-commuteᵉ (suc k) m >=>
        m+sk=n
    backward : Σ[ (fin-pair+ i n-i _) ∈ (FinPair+ n)] (Fin n-i) ->
               Σ[ (k , _) ∈ Fin n ] (FinPair+ k)
    backward ((fin-pair+ i n-i i+n-i=n) , (j , m , m+sj=n-i)) =
      ((i + j) , m , m+si+j=n) , (fin-pair+ i j refl)
      where
      m+si+j=n : m + (suc (i + j)) == n
      m+si+j=n =
        +-right (sym +'-right-suc) >=>
        sym (+-assocᵉ m i (suc j)) >=>
        +-left (+-commuteᵉ m i) >=>
        +-assocᵉ i m (suc j) >=>
        +-right m+sj=n-i >=>
        i+n-i=n

  Fin-FinPair+-triangle-Iso :
    Iso (Σ[ (k , _) ∈ Fin n ] (FinPair+ k)) (Σ[ (fin-pair+ i n-i _) ∈ (FinPair+ n)] (Fin n-i))
  Fin-FinPair+-triangle-Iso .Iso.fun = forward
  Fin-FinPair+-triangle-Iso .Iso.inv = backward
  Fin-FinPair+-triangle-Iso .Iso.leftInv x@((k , (m , m+sk=n)) , (fin-pair+ i j i+j=k)) =
    \ii -> p1 ii , p2 ii
    where
    p1 : fst (backward (forward x)) == fst x
    p1 = fin-j-path refl

    p2 : PathP (\i -> FinPair+ (Fin.i (p1 i))) (snd (backward (forward x))) (snd x)
    p2 = \ii -> fin-pair+ i j (ans ii)
      where
      ans : PathP (\ii -> ((i + j) == (Fin.i (p1 ii)))) refl i+j=k
      ans = isProp->PathP (\ii -> isSetNat _ _)
  Fin-FinPair+-triangle-Iso .Iso.rightInv x@((fin-pair+ i n-i i+n-i=n) , (j , m , m+sj=n-i)) =
    \ii -> p1 ii , p2 ii
    where
    p1 : fst (forward (backward x)) == fst x
    p1 = FinPair+-path₁ refl

    p2 : PathP (\ii -> Fin (FinPair+.j (p1 ii))) (snd (forward (backward x))) (snd x)
    p2 = \ii -> j , (ans ii)
      where
      ans : PathP (\ii -> (j < FinPair+.j (p1 ii)))
             (Fin.i<n (snd (forward (backward x)))) (Fin.i<n (snd x))
      ans = isProp->PathP (\ii -> isProp-<)
