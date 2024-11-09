{-# OPTIONS --cubical --safe --exact-split #-}

module real.integral.partition-refinement-join where

open import base
open import equality
open import equivalence
open import fin
open import fin.list
open import fin.list.sorted
open import fin.list.sorted-merge
open import functions
open import hlevel.base
open import lattice
open import nat
open import order
open import order.homomorphism
open import order.instances.fin
open import order.instances.integral-partition
open import order.instances.nat
open import order.instances.rational
open import rational
open import real
open import real.integral.partition
open import real.integral.partition-refinement
open import relation
open import sum
open import truncation

private
  NonEmpty : {ℓ : Level} {A : Type ℓ} -> Pred (FinList A) _
  NonEmpty {A = A} l = ∃ A (_l∈ l)

  expand-NonEmpty : {ℓ : Level} {A : Type ℓ} {l : FinList A} -> NonEmpty l ->
                    Σ[ m ∈ ℕ ] (Σ[ f ∈ (Fin (suc m) -> A) ] ((suc m , f) == l))
  expand-NonEmpty {l = suc n , f} _ = n , f , refl
  expand-NonEmpty {A = A} {l = 0 , f} e =
    bot-elim (unsquash isPropBot (∥-bind handle e))
    where
    handle : Σ A (_l∈ (0 , f)) -> ∥ Bot ∥
    handle (a , a∈) = ∥-map (¬fin-zero ∘ fst) a∈


  module _ (a b : ℝ) (p1 p2 : Partition a b) where
    private
      module p1 = Partition p1
      module p2 = Partition p2

    join-points : SortedList ℚ
    join-points = ∃!-val (sorted-merge p1.points p2.points)

    jp-eq : ∀ x -> ((x sl∈ join-points) ≃ (∥ x sl∈ p1.points ⊎ x sl∈ p2.points ∥))
    jp-eq = ∃!-prop (sorted-merge p1.points p2.points)


    q : ℚ
    q = p1.u zero-fin

    q∈jp : q sl∈ join-points
    q∈jp = eqInv (jp-eq q) (∣ inj-l (∣ zero-fin , refl ∣) ∣)

    NonEmpty-join-points : NonEmpty ⟨ join-points ⟩
    NonEmpty-join-points = ∣ q , q∈jp ∣

    join-points' : FinList ℚ
    join-points' = (suc (fst Σmf) , fst (snd Σmf))
      where
      Σmf = expand-NonEmpty NonEmpty-join-points

    jp-path : join-points' == ⟨ join-points ⟩
    jp-path = snd (snd (expand-NonEmpty NonEmpty-join-points))

    n : ℕ
    n = (pred (fst join-points'))
    u : Fin (suc n) -> ℚ
    u = (snd join-points')

    u0 : ℚ
    u0 = u zero-fin

    u0∈jp : u0 sl∈ join-points
    u0∈jp = subst (u0 l∈_) jp-path (∣ zero-fin , refl ∣)

    aU-u0 : Real.U a u0
    aU-u0 =
      unsquash (Real.isProp-U a u0)
        (∥-bind (either (∥-map handle1) (∥-map handle2)) (eqFun (jp-eq u0) u0∈jp))
      where
      handle1 : u0 sl∈' p1.points -> Real.U a u0
      handle1 (i , p) = subst (Real.U a) p (p1.aU-ui i)
      handle2 : u0 sl∈' p2.points -> Real.U a u0
      handle2 (i , p) = subst (Real.U a) p (p2.aU-ui i)

    un : ℚ
    un = u (n , refl-≤)

    un∈jp : un sl∈ join-points
    un∈jp = subst (un l∈_) jp-path (∣ (n , refl-≤) , refl ∣)

    bL-un : Real.L b un
    bL-un =
      unsquash (Real.isProp-L b un)
        (∥-bind (either (∥-map handle1) (∥-map handle2)) (eqFun (jp-eq un) un∈jp))
      where
      handle1 : un sl∈' p1.points -> Real.L b un
      handle1 (i , p) = subst (Real.L b) p (p1.bL-ui i)
      handle2 : un sl∈' p2.points -> Real.L b un
      handle2 (i , p) = subst (Real.L b) p (p2.bL-ui i)

    u<u : (i : Fin n) -> u (inc-fin i) < u (suc-fin i)
    u<u i = LinearOrderʰ.preserves-< h (fin< refl-≤)
      where
      h : LinearOrderʰ u
      h = subst Sorted (sym jp-path) (snd join-points)

    join-partition : Partition a b
    join-partition = record
      { n = n
      ; u = u
      ; aU-u0 = aU-u0
      ; bL-un = bL-un
      ; u<u = u<u
      }

    p1≤join-partition : p1 ≤ join-partition
    p1≤join-partition .Partition≼.refines .Sorted≼.indexes i = ans
      where
      ans : Σ[ j ∈ Fin (suc n) ] p1.u i == u j
      ans = handle (subst (p1.u i l∈'_) (sym jp-path)
                     (unsquash (isProp-sl∈' (p1.u i) join-points)
                       (eqInv (jp-eq (p1.u i)) (∣ inj-l (∣ i , refl ∣) ∣))))
        where
        handle : p1.u i l∈' join-points' -> Σ[ j ∈ Fin (suc n) ] p1.u i == u j
        handle (j , p) = j , sym p

    p2≤join-partition : p2 ≤ join-partition
    p2≤join-partition .Partition≼.refines .Sorted≼.indexes i = ans
      where
      ans : Σ[ j ∈ Fin (suc n) ] p2.u i == u j
      ans = handle (subst (p2.u i l∈'_) (sym jp-path)
                     (unsquash (isProp-sl∈' (p2.u i) join-points)
                       (eqInv (jp-eq (p2.u i)) (∣ inj-r (∣ i , refl ∣) ∣))))
        where
        handle : p2.u i l∈' join-points' -> Σ[ j ∈ Fin (suc n) ] p2.u i == u j
        handle (j , p) = j , sym p

    join-partition-least-≤ :
      (p3 : Partition a b) -> p1 ≤ p3 -> p2 ≤ p3 -> join-partition ≤ p3
    join-partition-least-≤ p3 p1≤p3 p2≤p3
      .Partition≼.refines .Sorted≼.indexes i =
        swap (unsquash (isProp-sl∈' (u i) p3.points) ans')
      where
      module p3 = Partition p3
      module r13 = Partition≼ p1≤p3
      module r23 = Partition≼ p2≤p3

      ans' : u i sl∈ p3.points
      ans' = ∥-bind handle (eqFun (jp-eq (u i)) (subst (u i l∈_) jp-path (∣ i , refl ∣)))
        where
        handle : (u i sl∈ p1.points ⊎ u i sl∈ p2.points) -> u i sl∈ p3.points
        handle (inj-l ui∈p1) = Sorted≼.preserves-∈ r13.refines ui∈p1
        handle (inj-r ui∈p2) = Sorted≼.preserves-∈ r23.refines ui∈p2

      swap : u i sl∈' p3.points -> Σ[ j ∈ Fin (suc p3.n) ] u i == p3.u j
      swap (j , p) = j , sym p


abstract
  instance
    JoinSemiLatticeStr-Partition≼ : {a b : ℝ} -> JoinSemiLatticeStr {D = Partition a b} useⁱ
    JoinSemiLatticeStr-Partition≼ {a} {b} = record
      { join = join-partition a b
      ; is-join-op = record
        { join-≤-left  = p1≤join-partition a b _ _
        ; join-≤-right = p2≤join-partition a b _ _
        ; join-least-≤ = join-partition-least-≤ a b _ _ _
        }
      }
