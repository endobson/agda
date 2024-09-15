{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.order.increasing.reflects where

open import additive-group
open import additive-group.instances.real
open import base
open import combinatorics.factorial
open import equality
open import fin
open import finset.instances
open import finsum.arithmetic
open import finsum.order
open import functions
open import funext
open import heyting-field.instances.real
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-field.mean
open import ordered-semiring
open import ordered-semiring.exponentiation
open import ordered-semiring.initial
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.exponential-series
open import real.exponential.order.increasing.preserves
open import real.exponential.order.positive
open import real.exponential.plus
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.order
open import real.series.geometric
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import semiring.instances.nat
open import sequence.partial-sums
open import truncation

private
  exp-≤-1+2x : {x : ℝ} -> 0# < x -> x < 1# -> exp x ≤ (1# + 2# * x)
  exp-≤-1+2x {x} 0<x x<1 = lt2
    where
    exp-term1+ : ∀ n -> exp-terms x (suc n) ≤ (x * (1/2 ^ℕ n))
    exp-term1+ n =
      trans-≤
        (subst2 _≤_ p2 p1
          (*₂-preserves-≤ (ℕ->Semiring-preserves-≤ (2^n≤factorial-suc n)) 0≤k))
        lt1
      where
      k : ℝ
      k = exp-terms x (suc n) * (1/2 ^ℕ n)
      0≤k : 0# ≤ k
      0≤k = weaken-< (*-preserves-0< (*-preserves-0< (0<1/ℕ _) (^ℕ-preserves-0< 0<x (suc n)))
                                     (^ℕ-preserves-0< 0<1/2 n))

      p1 : (ℕ->Semiring (factorial (suc n)) * k) == (x ^ℕ (suc n)) * (1/2 ^ℕ n)
      p1 = (*-right *-assoc >=> sym *-assoc >=>
            *-left (∃!-prop (∃!1/ℕ (factorial⁺ (suc n)))) >=>
            *-left-one)

      lt1 : ((x ^ℕ (suc n)) * (1/2 ^ℕ n)) ≤ (x * (1/2 ^ℕ n))
      lt1 = *₂-preserves-≤
        (trans-≤-=
          (*₁-preserves-≤ (weaken-< 0<x)
            (trans-≤-= (^ℕ-0≤-preserves-≤ (weaken-< 0<x) n (weaken-< x<1))
                       (^ℕ-preserves-1# n)))
          *-right-one)
        (^ℕ-preserves-0≤ (weaken-< 0<1/2) n)


      p2 : ((ℕ->Semiring (2 ^ℕ n)) * k) == exp-terms x (suc n)
      p2 = *-right *-commute >=>
           sym *-assoc >=>
           *-left (*-left (Semiringʰ-preserves-^ℕ (∃!-prop ∃!ℕ->Semiring) n) >=>
                   sym (^ℕ-distrib-*-right n) >=>
                   cong (_^ℕ n) (∃!-prop (∃!1/ℕ _)) >=>
                   ^ℕ-preserves-1# n)>=>
           *-left-one


    ps : ∀ n -> partial-sums (exp-terms x ∘ suc ∘ suc) n ≤
                partial-sums (\i -> x * ((1/2 ^ℕ (suc i)))) n
    ps n = finiteSum-preserves-≤ (\(i , _) -> (exp-term1+ (suc i)))

    lim1 : isLimit (partial-sums (exp-terms x ∘ suc ∘ suc)) (diff (1# + x) (exp x))
    lim1 = subst2 isLimit (funExt p1) refl
             (diff-preserves-limit
               (isLimit-constant-seq (1# + x))
               (dropN-preserves-limit (isLimit-exp x)))
       where
       p1 : ∀ n -> diff (1# + x) (partial-sums (exp-terms x) (suc (suc n))) ==
                   partial-sums (exp-terms x ∘ suc ∘ suc) n
       p1 n = +-left (partial-sums-suc >=> +-right partial-sums-suc >=> sym +-assoc >=>
                      +-commute) >=>
              +-assoc >=>
              +-right (+-left (+-cong exp-term0 exp-term1) >=>
                       +-inverse) >=>
              +-right-zero

    lim2 : isLimit (partial-sums (\i -> x * ((1/2 ^ℕ (suc i))))) x
    lim2 = lim-geo4
      where
      ∣1/2∣<1 : abs 1/2 < 1#
      ∣1/2∣<1 = (trans-=-< (abs-0≤-path (weaken-< 0<1/2)) 1/2<1)
      v : ℝ
      v = geometric-series-limit 1/2 ∣1/2∣<1
      lim-geo : isLimit (partial-sums (1/2 ^ℕ_)) v
      lim-geo = isLimit-geometric-series 1/2 ∣1/2∣<1
      d-path : diff 1/2 1# == 1/2
      d-path = +-left (sym 1/2-+-path) >=> +-assoc >=> +-right +-inverse >=> +-right-zero
      v=2 : v == 2#
      v=2 =
        sym *-right-one >=>
        *-right (sym 2*1/2-path >=> *-commute) >=>
        sym *-assoc >=>
        *-left (*-right (sym d-path) >=> geometric-series-limit-path _ _) >=>
        *-left-one

      lim-geo2 : isLimit (\n -> 1# + partial-sums (1/2 ^ℕ_ ∘ suc) n) 2#
      lim-geo2 = subst2 isLimit (funExt (\_ -> partial-sums-suc)) v=2
                        (dropN-preserves-limit lim-geo)

      lim-geo3 : isLimit (partial-sums (1/2 ^ℕ_ ∘ suc)) 1#
      lim-geo3 =
        subst2 isLimit (funExt (\n -> (+-assoc >=> diff-step))) (+-assoc >=> diff-step)
          (+-preserves-limit lim-geo2 (isLimit-constant-seq (- 1#)))

      lim-geo4 : isLimit (partial-sums (\i -> x * ((1/2 ^ℕ (suc i))))) x
      lim-geo4 = subst2 isLimit (funExt (\_ -> (sym finiteSum-*))) *-right-one
                  (*₁-preserves-limit lim-geo3)

    lt1 : (diff (1# + x) (exp x)) ≤ x
    lt1 = isLimit-preserves-≤ lim1 lim2 ps
    lt2 : exp x ≤ (1# + 2# * x)
    lt2 = subst2 _≤_ diff-step (+-assoc >=> +-right (sym 2*-path)) (+₁-preserves-≤ lt1)


  exp-1<-implies-0< : {x : ℝ} -> 1# < exp x -> 0# < x
  exp-1<-implies-0< {x} 1<ex = unsquash isProp-< (∥-map handle (comparison-< _ x _ 0<ε2))
    where
    m : ℝ
    m = mean 1# (exp x)
    ε : ℝ
    ε = diff 1# m
    0<ε : 0# < ε
    0<ε = diff-0<⁺ (mean-<₁ 1<ex)

    ε/2 : ℝ
    ε/2 = ε * 1/2
    0<ε/2 : 0# < ε/2
    0<ε/2 = *-preserves-0< 0<ε 0<1/2

    ε2 : ℝ
    ε2 = min 1/2 (ε * 1/2)
    0<ε2 : 0# < ε2
    0<ε2 = min-greatest-< 0<1/2 0<ε/2

    ε2<1 : ε2 < 1#
    ε2<1 = trans-≤-< min-≤-left 1/2<1

    1+ε<ex : (1# + ε) < exp x
    1+ε<ex = trans-=-< diff-step (mean-<₂ 1<ex)

    ¬x<ε2 : ¬ (x < ε2)
    ¬x<ε2 x<ε2 = asym-< 1+ε<ex (trans-<-≤ ex<eε2 eε2≤1+ε)
      where
      eε2≤1+ε : exp ε2 ≤ (1# + ε)
      eε2≤1+ε =
        trans-≤-= (trans-≤ (exp-≤-1+2x 0<ε2 ε2<1)
                           (+₁-preserves-≤ (*₁-preserves-≤ (weaken-< 0<2) min-≤-right)))
          (+-right (*-right *-commute >=> sym *-assoc >=> *-left 2*1/2-path >=> *-left-one))

      ex<eε2 : exp x < exp ε2
      ex<eε2 = exp-preserves-< x<ε2

    handle : (0# < x) ⊎ (x < ε2) -> 0# < x
    handle (inj-l 0<x) = 0<x
    handle (inj-r x<ε2) = bot-elim (¬x<ε2 x<ε2)

opaque
  exp-reflects-< : {x y : ℝ} -> exp x < exp y -> x < y
  exp-reflects-< {x} {y} ex<ey = diff-0<⁻ (exp-1<-implies-0< 1<e[dxy])
    where
    1<e[dxy] : 1# < exp (diff x y)
    1<e[dxy] = subst2 _<_ exp-minus-inverse (sym (exp-+-path y (- x)))
                (*₂-preserves-< ex<ey exp-0<)
