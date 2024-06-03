{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.nth-root where

open import additive-group
open import base
open import equality
open import functions
open import isomorphism
open import nat.even-odd
open import order
open import order.instances.nat
open import order.instances.rational
open import ordered-additive-group
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.open-interval
open import rational.open-interval.containment
open import rational.open-interval.sequence
open import rational.order
open import real
open import real.arithmetic.nth-root.bound-sequence
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import sequence
open import truncation

isNthRoot : (n : Nat) (x : ℝ) (y : ℝ) -> Type₁
isNthRoot n x y = x ^ℕ n == y

module _
  (n : Nat)
  (odd-n : Odd n)
  (x : ℝ)
  where

  private
    module x = Real x

    ^ℕ-isDense : ∀ {q r : ℚ} -> q < r -> ∃[ a ∈ ℚ ] (q < (a ^ℕ n) × (a ^ℕ n) < r)
    ^ℕ-isDense {q} {r} q<r = ∥-bind handle-mid (dense-< q<r)
      where
      Ans : Type₀
      Ans = ∃[ a ∈ ℚ ] (q < (a ^ℕ n) × (a ^ℕ n) < r)
      module _ ((m , q<m , m<r) : Σ[ m ∈ ℚ ] (q < m × m < r)) where
        i1 : Iℚ
        i1 = Iℚ-cons q r (trans-< q<m m<r)
        s : Sequence Iℚ
        s = Root-seq (n , odd-n) m

        root-bound : ∀ i -> Σ[ l ∈ ℚ ] (l ^ℕ n == Iℚ.l (s i))
        root-bound = Root-root-bound (n , odd-n) m

        m∈s : ∀ n -> ℚ∈Iℚ m (s n)
        m∈s = Root-q∈s (n , odd-n) m
        small-s : ArbitrarilySmall (i-width ∘ s)
        small-s = Root-small-s (n , odd-n) m

        s⊂i1 : ∀Largeℕ (\n -> s n i⊂ i1)
        s⊂i1 = ArbitrarilySmall->i⊂ s small-s m∈s i1 (q<m , m<r)

        module _ (idx : Nat) (si⊂i1 : s idx i⊂ i1)
          where
          module si⊂i1 = _i⊂_ si⊂i1

          Σroot-lsi : Σ[ l ∈ ℚ ] (l ^ℕ n == Iℚ.l (s idx))
          Σroot-lsi = root-bound idx

          handle-idx : Ans
          handle-idx =
            ∣ fst Σroot-lsi ,
              trans-<-= si⊂i1.l (sym (snd Σroot-lsi)) ,
              trans-=-< (snd Σroot-lsi) (trans-< (Iℚ.l<u (s idx)) si⊂i1.u) ∣

        handle-mid : Ans
        handle-mid = ∥-bind (\(i , f) -> handle-idx i (f i refl-≤)) s⊂i1


    ^ℕ-preserves-< : ∀ {q r : ℚ} -> q < r -> (q ^ℕ n) < (r ^ℕ n)
    ^ℕ-preserves-< = Iso.fun (x<y<->x^n<y^n n odd-n _ _)
    ^ℕ-reflects-< : ∀ {q r : ℚ} -> (q ^ℕ n) < (r ^ℕ n) -> q < r
    ^ℕ-reflects-< = Iso.inv (x<y<->x^n<y^n n odd-n _ _)

    L : Pred ℚ ℓ-zero
    L q = x.L (q ^ℕ n)
    U : Pred ℚ ℓ-zero
    U q = x.U (q ^ℕ n)

    isLowerSet-L : isLowerSet L
    isLowerSet-L q<r Lr = x.isLowerSet-L (^ℕ-preserves-< q<r) Lr
    isUpperSet-U : isUpperSet U
    isUpperSet-U q<r Lq = x.isUpperSet-U (^ℕ-preserves-< q<r) Lq

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-bind handle x.Inhabited-L
      where
      handle : Σ ℚ x.L -> ∃ ℚ L
      handle (q , xL-q) = ∥-bind handle2 (^ℕ-isDense q1<q)
        where
        q1 : ℚ
        q1 = (q + (- 1#))
        q1<q : q1 < q
        q1<q = trans-<-= (+₁-preserves-< (minus-flips-0< 0<1)) +-right-zero

        handle2 : Σ[ a ∈ ℚ ] (q1 < (a ^ℕ n) × (a ^ℕ n) < q) -> ∃ ℚ L
        handle2 (a , _ , a^n<q) = ∣ a , x.isLowerSet-L a^n<q xL-q ∣

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-bind handle x.Inhabited-U
      where
      handle : Σ ℚ x.U -> ∃ ℚ U
      handle (q , xU-q) = ∥-bind handle2 (^ℕ-isDense q<q1)
        where
        q1 : ℚ
        q1 = (q + 1#)
        q<q1 : q < q1
        q<q1 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1)

        handle2 : Σ[ a ∈ ℚ ] (q < (a ^ℕ n) × (a ^ℕ n) < q1) -> ∃ ℚ U
        handle2 (a , q<a^n , _) = ∣ a , x.isUpperSet-U q<a^n xU-q ∣

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q Lq = ∥-bind handle (x.isUpperOpen-L _ Lq)
      where
      handle : Σ[ r ∈ ℚ ] ((q ^ℕ n) < r × x.L r) -> _
      handle (r , q^n<r , xL-r) = ∥-bind handle2 (^ℕ-isDense q^n<r)
        where
        handle2 : Σ[ p ∈ ℚ ] ((q ^ℕ n) < (p ^ℕ n) × (p ^ℕ n) < r) -> _
        handle2 (p , q^n<p^n , p^n<r) = ∣ p , ^ℕ-reflects-< q^n<p^n , x.isLowerSet-L p^n<r xL-r ∣

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q Uq = ∥-bind handle (x.isLowerOpen-U _ Uq)
      where
      handle : Σ[ r ∈ ℚ ] (r < (q ^ℕ n) × x.U r) -> _
      handle (r , r<q^n , xU-r) = ∥-bind handle2 (^ℕ-isDense r<q^n)
        where
        handle2 : Σ[ p ∈ ℚ ] (r < (p ^ℕ n) × (p ^ℕ n) < (q ^ℕ n)) -> _
        handle2 (p , r<p^n , p^n<q^n) = ∣ p , ^ℕ-reflects-< p^n<q^n , x.isUpperSet-U r<p^n xU-r ∣

    disjoint : Universal (Comp (L ∩ U))
    disjoint _ = x.disjoint _

    located : (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located _ _ q<r = x.located _ _ (^ℕ-preserves-< q<r)


    nthRoot : ℝ
    nthRoot = record
      { L = L
      ; U = U
      ; isProp-L = \_ -> x.isProp-L _
      ; isProp-U = \_ -> x.isProp-U _
      ; Inhabited-L = Inhabited-L
      ; Inhabited-U = Inhabited-U
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; disjoint = disjoint
      ; located = located
      }
