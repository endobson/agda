{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.nth-root where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import hlevel
open import nat
open import nat.even-odd
open import nat.half-induction
open import order
open import order.instances.nat
open import order.instances.real
open import ordered-semiring.exponentiation
open import ordered-semiring.instances.real
open import real
open import real.arithmetic.nth-root.base
open import real.arithmetic.nth-root.odd
open import real.arithmetic.sqrt
open import real.arithmetic.sqrt.base
open import real.subspace
open import ring.implementations.real
open import semiring.exponentiation
open import sigma.base
open import subset.subspace
open import sum
open import truncation

private
  module _ (x∈@(x , 0≤x) : ℝ⁰⁺) where
    private
      module x = Real x

    isProp-Ans : ((n , _) : Nat⁺) -> isProp (Σ[ (y , _) ∈ ℝ⁰⁺ ] (isNthRoot n x y))
    isProp-Ans n⁺ ((y1 , 0≤y1) , y1^n=x) ((y2 , 0≤y2) , y2^n=x) =
      ΣProp-path (isSet-ℝ _ _) (Subspace-path y1=y2)
      where
      y1≤y2 : y1 ≤ y2
      y1≤y2 = ^ℕ-0≤-reflects-≤ 0≤y1 0≤y2 n⁺ (path-≤ (y1^n=x >=> sym y2^n=x))
      y2≤y1 : y2 ≤ y1
      y2≤y1 = ^ℕ-0≤-reflects-≤ 0≤y2 0≤y1 n⁺ (path-≤ (y2^n=x >=> sym y1^n=x))
      y1=y2 : y1 == y2
      y1=y2 = antisym-≤ y1≤y2 y2≤y1


    nthRoot' : (n⁺@(n , _) : Nat⁺) -> HalfIndCase⁺ n⁺ -> Σ[ (y , 0≤y) ∈ ℝ⁰⁺ ] (isNthRoot n x y)
    nthRoot' (n , _) (one-case p) =
      (oddNthRoot on x , oddNthRoot-preserves-0≤ on x 0≤x) ,
      isNthRoot-oddNthRoot on x
      where
      on : Σ Nat Odd
      on = (n , subst Odd (sym p) tt)
    nthRoot' (n , _) (odd-case _ _ _ _ odd-n) =
      (oddNthRoot (n , odd-n) x , oddNthRoot-preserves-0≤ (n , odd-n) x 0≤x) ,
      isNthRoot-oddNthRoot (n , odd-n) x
    nthRoot' (n , _) (even-case m⁺@(m , _) cm _ n=m+m even-n) =
      (sqrtℝ y∈ , sqrt-0≤ y∈) , isNthRoot-sy
      where
      rec = nthRoot' m⁺ cm
      y∈ = fst rec
      isNthRoot-sy : isNthRoot n x (sqrtℝ y∈)
      isNthRoot-sy =
        cong (sqrtℝ y∈ ^ℕ_) n=m+m >=>
        ^ℕ-distrib-+-left m m >=>
        sym (^ℕ-distrib-*-right m) >=>
        cong (_^ℕ m) (sqrt² y∈) >=>
        (snd rec)

opaque
  ∃!nthRoot : ((n , _) : Nat⁺) ((x , _) : ℝ⁰⁺) -> ∃![ (y , _) ∈ ℝ⁰⁺ ] (isNthRoot n x y)
  ∃!nthRoot n x∈ = nthRoot' x∈ n (half-ind-case⁺ n) , isProp-Ans x∈ n _

nthRoot : (n : Nat⁺) (x : ℝ⁰⁺) -> ℝ
nthRoot n x = Subspace.value (∃!-val (∃!nthRoot n x))
