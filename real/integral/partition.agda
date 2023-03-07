{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.partition where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import fin
open import fin.list.sorted
open import nat
open import nat.order.base
open import order
open import order.instances.fin
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import rational
open import real
open import real.integral.partition-index
open import real.rational
open import relation

record Partition (a : ℝ) (b : ℝ) : Type₀ where
  no-eta-equality
  pattern
  field
    n : ℕ
    u : Fin (suc n) -> ℚ
    aU-u0 : Real.U a (u zero-fin)
    bL-un : Real.L b (u (n , refl-≤))
    u<u : (i : Fin n) -> u (inc-fin i) < u (suc-fin i)

  uℝ : Fin (suc n) -> ℝ
  uℝ i = ℚ->ℝ (u i)

  uB : PartitionBoundary n -> ℝ
  uB pb-low     = a
  uB (pb-mid i) = (uℝ i)
  uB pb-high    = b

  a<u0 : a < uℝ zero-fin
  a<u0 = U->ℝ< aU-u0

  un<b : (uℝ (n , refl-≤)) < b
  un<b = L->ℝ< bL-un

  uℝ<uℝ : (i : Fin n) -> uℝ (inc-fin i) < uℝ (suc-fin i)
  uℝ<uℝ i = ℚ->ℝ-preserves-< _ _ (u<u i)

  interval-low : (i : PartitionIndex n) -> ℝ
  interval-low i = uB (fst (index->low-boundary i))

  interval-high : (i : PartitionIndex n) -> ℝ
  interval-high i = uB (fst (index->high-boundary i))

  width : (i : PartitionIndex n) -> ℝ
  width i = diff (interval-low i) (interval-high i)

  abstract
    u0≤ui : (i : Fin (suc n)) -> u zero-fin ≤ u i
    u0≤ui (i , lt) = handle i lt
      where
      handle : (i : Nat) -> (lt : i < suc n) -> u zero-fin ≤ u (i , lt)
      handle zero lt = path-≤ (cong u (fin-i-path refl))
      handle (suc i) lt =
        trans-≤ (handle i (trans-< refl-≤ lt))
                (weaken-< (subst2 _<_ (cong u (fin-i-path refl)) (cong u (fin-i-path refl))
                                  (u<u (i , pred-≤ lt))))


    a<ui : (i : Fin (suc n)) -> a < uℝ i
    a<ui i = trans-<-≤ a<u0 (ℚ->ℝ-preserves-≤ _ _ (u0≤ui i))


    ui≤un : (i : Fin (suc n)) -> u i ≤ u (n , refl-≤)
    ui≤un (i , j , path) = handle i j path
      where
      handle : (i j : Nat) -> (p : j + (suc i) == (suc n)) -> u (i , j , p) ≤ u (n , refl-≤)
      handle i zero path = path-≤ (cong u (fin-i-path (cong pred path)))
      handle i (suc j) path =
        trans-≤ (weaken-< (subst2 _<_ (cong u (fin-i-path refl)) (cong u (fin-i-path refl))
                                      (u<u (i , j , cong pred path))))
                (handle (suc i) j (+'-right-suc >=> path))

    ui<b : (i : Fin (suc n)) -> uℝ i < b
    ui<b i = trans-≤-< (ℚ->ℝ-preserves-≤ _ _ (ui≤un i)) un<b

    a<b : a < b
    a<b = (trans-< (a<ui zero-fin) (ui<b zero-fin))

    a≤uB : (i : PartitionBoundary n) -> a ≤ uB i
    a≤uB pb-low = refl-≤
    a≤uB (pb-mid i) = weaken-< (a<ui i)
    a≤uB pb-high = weaken-< a<b

    uB≤b : (i : PartitionBoundary n) -> uB i ≤ b
    uB≤b pb-low = weaken-< a<b
    uB≤b (pb-mid i) = weaken-< (ui<b i)
    uB≤b pb-high = refl-≤

    low-boundary<b : (i : Σ (PartitionBoundary n) LowPartitionBoundary) -> uB ⟨ i ⟩ < b
    low-boundary<b (pb-low   , _) = a<b
    low-boundary<b (pb-mid i , _) = ui<b i

    a<high-boundary : (i : Σ (PartitionBoundary n) HighPartitionBoundary) -> a < uB ⟨ i ⟩
    a<high-boundary (pb-mid i , _) = a<ui i
    a<high-boundary (pb-high   , _) = a<b

    u-preserves-< : {i j : Fin (suc n)} -> i < j -> u i < u j
    u-preserves-< {i , i<n} {j , j<n} (fin< (k , kp)) = handle i j i<n j<n k kp
      where
      handle : (i j : Nat) -> (i<sn : i < (suc n)) -> (j<sn : j < (suc n)) ->
               (k : Nat) -> (k + (suc i) == j) ->
               u (i , i<sn) < u (j , j<sn)
      handle i zero     _ _ k kp = bot-elim (zero-≮ (k , kp))
      handle i (suc j') _ j<sn zero kp =
        subst2 _<_ (cong u (fin-i-path refl)) (cong u (fin-i-path kp))
               (u<u (i , pred-≤ (trans-≤-< (zero , kp) j<sn)))
      handle i (suc j') i<sn j<sn (suc k) kp =
        trans-< (handle i j' i<sn (trans-< refl-≤ j<sn) k (cong pred kp))
                (subst2 _<_ (cong u (fin-i-path refl)) (cong u (fin-i-path refl))
                        (u<u (j' , pred-≤ j<sn)))

    uB-preserves-< : {i j : PartitionBoundary n} -> i < j -> uB i < uB j
    uB-preserves-< (pb<-low-mid i)  = a<high-boundary _
    uB-preserves-< (pb<-low-high)   = a<b
    uB-preserves-< (pb<-mid-high i) = low-boundary<b _
    uB-preserves-< (pb<-mid-mid i j lt) = ℚ->ℝ-preserves-< _ _ (u-preserves-< lt)

    uB-preserves-≤ : {i j : PartitionBoundary n} -> i ≤ j -> uB i ≤ uB j
    uB-preserves-≤ {i} {j} i≤j uBj<uBi = handle (trichotomous-< i j)
      where
      handle : Tri< i j -> Bot
      handle (tri< i<j _ _) = asym-< (uB-preserves-< i<j) uBj<uBi
      handle (tri= _ i=j _) = irrefl-< (trans-<-= uBj<uBi (cong uB i=j))
      handle (tri> _ _ j<i) = i≤j j<i



    0<width : (i : PartitionIndex n) -> 0# < width i
    0<width pi-low = trans-=-< (sym +-inverse) (+₂-preserves-< a<u0)
    0<width (pi-mid i) = trans-=-< (sym +-inverse) (+₂-preserves-< (uℝ<uℝ i))
    0<width pi-high = trans-=-< (sym +-inverse) (+₂-preserves-< un<b)

  points : SortedList ℚ
  points = (suc n , u) , record { preserves-< = u-preserves-< }

partition->< : {a b : ℝ} -> Partition a b -> a < b
partition->< p =
  trans-< (Partition.a<ui p zero-fin) (Partition.ui<b p zero-fin)

isδFine : {a b : ℝ} (δ : ℝ) (p : Partition a b) -> Type₁
isδFine δ p = (i : PartitionIndex p.n) -> p.width i ≤ δ
  where
  module p = Partition p

weaken-isδFine : {a b : ℝ} {δ1 δ2 : ℝ} -> δ1 ≤ δ2 -> (p : Partition a b) ->
                          isδFine δ1 p -> isδFine δ2 p
weaken-isδFine δ1≤δ2 _ f i = trans-≤ (f i) δ1≤δ2
