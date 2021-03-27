{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.partition where

open import base
open import nat
open import functions
open import vec
open import hlevel
open import sigma
open import relation
open import equality
open import commutative-monoid
open import truncation
open import equivalence
open import cubical
open import fin-algebra
open import fin
open import ring
open import ring.implementations

private
  variable
    ℓ : Level
    A : Type ℓ

-- private
--   DSet : Type ℓ -> Type ℓ
--   DSet A = A -> Boolean
-- 
-- empty-set : DSet A
-- empty-set _ = false
-- 
-- data Fin : Nat -> Type₀ where
--   zero : {n : Nat} -> Fin (suc n)
--   suc  : {n : Nat} -> Fin n -> Fin (suc n)
-- 
-- FinZero : {n : Nat} -> Fin n -> Set
-- FinZero zero    = Top
-- FinZero (suc _) = Bot
-- 
-- fin-zero!=suc : {n : Nat} {x : Fin n} -> zero != suc x
-- fin-zero!=suc p = bot-elim (transport (cong FinZero p) tt)
-- 
-- fin-pred : {n : Nat} -> Fin (suc (suc n)) -> Fin (suc n)
-- fin-pred zero    = zero
-- fin-pred (suc x) = x
-- 
-- fin-suc-injective : {n : Nat} {x y : Fin n} -> Path (Fin (suc n)) (suc x) (suc y) -> x == y
-- fin-suc-injective {suc n} p = cong fin-pred p
-- 
-- decide-fin : {n : Nat} -> (x y : Fin n) -> Dec (x == y)
-- decide-fin zero    zero    = yes refl
-- decide-fin zero    (suc y) = no fin-zero!=suc
-- decide-fin (suc _) zero    = no (fin-zero!=suc ∘ sym)
-- decide-fin (suc x) (suc y) with decide-fin x y
-- ... | (yes p) = yes (cong suc p)
-- ... | (no f) = no (f ∘ fin-suc-injective)
-- 
-- 
-- 
-- 
-- vec-ref : {n : Nat} -> Vec A n -> Fin n -> A
-- vec-ref (a :: _) zero    = a
-- vec-ref (_ :: v) (suc n) = vec-ref v n
-- 
-- vec-set : {n : Nat} -> Vec A n -> Fin n -> A -> Vec A n
-- vec-set (_ :: v) zero    a2 = a2 :: v
-- vec-set (a :: v) (suc n) a2 = a  :: (vec-set v n a2)
-- 
-- vec-ref-set-same-index' : {n : Nat} {a : A} (v : Vec A n) (i : Fin n)
--                          -> vec-ref (vec-set v i a) i == a
-- vec-ref-set-same-index' (_ :: _) zero    = refl
-- vec-ref-set-same-index' (_ :: v) (suc i) = vec-ref-set-same-index' v i
-- 
-- vec-ref-set-same-index : {n : Nat} {a : A} (v : Vec A n) {i j : Fin n} (p : i == j)
--                          -> vec-ref (vec-set v i a) j == a
-- vec-ref-set-same-index {a = a} v {i} {j} p =
--   (\k -> vec-ref (vec-set v i a) (p (~ k))) >=> vec-ref-set-same-index' v i
-- 
-- vec-ref-set-different-index : {n : Nat} {a : A} (v : Vec A n) {i j : Fin n} (p : i != j)
--                               -> vec-ref (vec-set v i a) j == vec-ref v j
-- vec-ref-set-different-index (_ :: _) {zero } {suc _} _ = refl
-- vec-ref-set-different-index (_ :: _) {suc _} {zero } _ = refl
-- vec-ref-set-different-index (_ :: _) {zero } {zero } p = bot-elim (p refl)
-- vec-ref-set-different-index (_ :: v) {suc _} {suc _} p =
--   vec-ref-set-different-index v (p ∘ (cong suc))
-- 
-- vec-update : {n : Nat} -> Vec A n -> Fin n -> (A -> A) -> Vec A n
-- vec-update v i f = vec-set v i (f (vec-ref v i))
-- 
-- fun->vec : {n : Nat} -> (Fin n -> A) -> Vec A n
-- fun->vec {n = zero}    f = []
-- fun->vec {n = (suc n)} f = (f zero) :: (fun->vec (f ∘ suc))
-- 
-- 
-- partition : {n : Nat} -> DSet A -> (A -> Fin n) -> Vec (DSet A) n
-- partition {A = A} {n = n} member part = fun->vec f
--   where
--   f : Fin n -> A -> Boolean
--   f i a with decide-fin i (part a)
--   ... | (yes p) = (member a)
--   ... | (no _) = false


--record FiniteSum {D : Type ℓ} (M : CommMonoid D) : Type (ℓ-suc ℓ) where
--  field
--    I : Type ℓ
--    P : Pred I ℓ
--    f : I -> D



module _ {D : Type ℓ} (S : Semiring D) where
  open Semiring S

  finSumDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finSumDep zero    _ = 0#
  finSumDep (suc n) f = f zero-fin + (finSumDep n (f ∘ suc-fin))

  i<nSum : (n : Nat) -> (f : Nat -> D) -> D
  i<nSum n f = finSumDep n (\ (x , _) -> f x)

  enumerationSum : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationSum = ?

i<nSum-zero : {n : Nat} -> i<nSum NatSemiring n (\i -> 0) == 0
i<nSum-zero {n = zero}  = refl
i<nSum-zero {n = suc n} = i<nSum-zero {n}

i<nSum-one : {n : Nat} -> i<nSum NatSemiring n (\i -> 1) == n
i<nSum-one {n = zero}  = refl
i<nSum-one {n = suc n} = cong suc (i<nSum-one {n})

--transferProperty : (P : Pred Type₀ ℓ)
--                   (pProp : (n : Nat) -> (isProp (P (Fin n)))) 
--                   -> Nat
--transferProperty _ _ = 0
  


--fms-add : FinMultiSet A -> A -> FinMultiSet A
--fms-add (n , v) a = (suc n , a :: v)
--
--partition : {n : Nat} -> FinMultiSet A -> (A -> Fin n) -> MultiSet (FinMultiSet A) n
--partition {A = A} {n = n} (s , v) part = partition' v (n-times n empty-ms)
--  where
--  partition' : {m : Nat} -> Vec A m -> MultiSet (FinMultiSet A) n -> MultiSet (FinMultiSet A) n
--  partition' []       acc = acc
--  partition' (a :: v) acc = (partition' v (vec-update acc (part a) (\fms -> fms-add fms a)))
