{-# OPTIONS --cubical --safe --exact-split #-}

module combinatorics.triangle-numbers where

open import additive-group
open import additive-group.instances.nat
open import base
open import combinatorics.binomial-coefficients
open import decision
open import equality-path
open import fin
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.small
open import finset
open import finset.instances
open import finset.search
open import finsum
open import hlevel.base
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import relation
open import semiring
open import semiring.instances.nat
open import sum
open import truncation

triangle-number-recursive : ℕ -> ℕ
triangle-number-recursive zero = zero
triangle-number-recursive (suc n) = (suc n) + triangle-number-recursive n

opaque
  triangle-number : ℕ -> ℕ
  triangle-number = triangle-number-recursive

  triangle-number-recursive-path : ∀ n -> triangle-number-recursive n == triangle-number n
  triangle-number-recursive-path n = refl

opaque
  unfolding triangle-number

  triangle-number-quadratic-path :
    ∀ (n : ℕ) -> n * (suc n) == 2 * triangle-number n
  triangle-number-quadratic-path zero =
    sym (*-right-zeroᵉ 2) >=>
    (\i -> 2 * (triangle-number-recursive-path zero i))
  triangle-number-quadratic-path (suc n) =
    step₁ >=> cong ((2 * suc n) +_) rec >=> sym step₂
    where
    rec : n * (suc n) == 2 * triangle-number n
    rec = triangle-number-quadratic-path n

    step₁ : (suc n) * (suc (suc n)) == 2 * (suc n) + n * (suc n)
    step₁ =
      (*-commuteᵉ (suc n) (suc (suc n))) >=>
      sym (+-assocᵉ (suc n) (suc n) (n * (suc n))) >=>
      cong (_+ (n * suc n)) (cong suc (cong (n +_) (sym (*-left-oneᵉ (suc n)))))

    step₂ : 2 * triangle-number (suc n) ==
            2 * (suc n) +  2 * triangle-number n
    step₂ = *-distrib-+-leftᵉ 2 (suc n) (triangle-number-recursive n)


triangle-number-binomial : ℕ -> ℕ
triangle-number-binomial zero = zero
triangle-number-binomial (suc n) = binomial-coeff' n 2

opaque
  unfolding triangle-number

  triangle-number-binomial-path : ∀ n -> triangle-number-binomial n == triangle-number n
  triangle-number-binomial-path zero = triangle-number-recursive-path zero
  triangle-number-binomial-path (suc zero) =
    triangle-number-recursive-path (suc zero)
  triangle-number-binomial-path (suc (suc n)) =
    cong2 _+_ (triangle-number-binomial-path (suc n))
              (binomial-coeff'-one₂ (suc n)) >=>
    +-commuteᵉ (triangle-number-recursive (suc n)) (suc (suc n))


triangle-number-finiteSum : ℕ -> ℕ
triangle-number-finiteSum n = finiteSum (\ ((i , _) : Fin n) -> suc i)

opaque
  unfolding triangle-number

  triangle-number-finiteSum-path : ∀ n -> triangle-number-finiteSum n == triangle-number n
  triangle-number-finiteSum-path zero = finiteMerge-Fin0
  triangle-number-finiteSum-path (suc n) =
    finiteMerge-FinSuc' >=>
    cong (suc n +_) (triangle-number-finiteSum-path n)


-- Order
opaque
  unfolding triangle-number

  private
   triangle-number-suc : ∀ n -> triangle-number n < triangle-number (suc n)
   triangle-number-suc n = +₂-preserves-< zero-<

  triangle-number-inflationary : ∀ n -> n ≤ triangle-number n
  triangle-number-inflationary zero = refl-≤
  triangle-number-inflationary (suc n) =
    trans-≤ (suc-≤ (triangle-number-inflationary n))
            (triangle-number-suc n)

private
  triangle-number-≤ : ∀ i n -> triangle-number n ≤ triangle-number (i + n)
  triangle-number-≤ zero n = refl-≤
  triangle-number-≤ (suc i) n =
    trans-≤ (triangle-number-≤ i n) (weaken-< (triangle-number-suc (i + n)))

opaque
  triangle-number-preserves-< : {n₁ n₂ : ℕ} -> n₁ < n₂ -> triangle-number n₁ < triangle-number n₂
  triangle-number-preserves-< {n₁} {n₂} (i , p) =
    trans-≤-< (triangle-number-≤ i n₁)
      (trans-<-= (triangle-number-suc (i + n₁))
                 (cong triangle-number (sym +'-right-suc >=> p)))

  triangle-number-preserves-≤ : {n₁ n₂ : ℕ} -> n₁ ≤ n₂ -> triangle-number n₁ ≤ triangle-number n₂
  triangle-number-preserves-≤ {n₁} {n₂} n₁≤n₂ = case (split-< n₁ n₂) of
    (\{ (inj-l n₁<n₂) -> weaken-< (triangle-number-preserves-< n₁<n₂)
      ; (inj-r n₂≤n₁) -> path-≤ (cong triangle-number (antisym-≤ n₁≤n₂ n₂≤n₁))
      })




isTriangleNumber : ℕ -> Type₀
isTriangleNumber n = Σ[ i ∈ ℕ ] (triangle-number i == n)

opaque
  isProp-isTriangleNumber : ∀ n -> isProp (isTriangleNumber n)
  isProp-isTriangleNumber n (i₁ , p₁) (i₂ , p₂) = \k -> ip k , pp k
    where
    tp : triangle-number i₁ == triangle-number i₂
    tp = p₁ >=> sym p₂


    ip : i₁ == i₂
    ip = case (trichotomous-< i₁ i₂) of (\
      { (tri< i₁<i₂ _ _) -> bot-elim (irrefl-path-< tp (triangle-number-preserves-< i₁<i₂))
      ; (tri= _ i₁=i₂ _) -> i₁=i₂
      ; (tri> _ _ i₂<i₁) -> bot-elim (irrefl-path-< (sym tp) (triangle-number-preserves-< i₂<i₁))
      })

    pp : PathP (\k -> triangle-number (ip k) == n) p₁ p₂
    pp = isProp->PathP (\k -> isSetNat (triangle-number (ip k)) n)

opaque
  decide-isTriangleNumber : ∀ n -> Dec (isTriangleNumber n)
  decide-isTriangleNumber n = either pos-case neg-case cases
    where
    dec-fin : ∀ ((i , _) : Fin (suc n)) -> Dec (triangle-number i == n)
    dec-fin _ = decide-nat _ _

    cases : (∃[ (i , _) ∈ Fin (suc n) ] (triangle-number i == n)) ⊎
            (∀ ((i , _) : Fin (suc n)) -> triangle-number i != n)
    cases = finite-search-dec (_ , isFinSetⁱ) dec-fin

    pos-case : ∃[ (i , _) ∈ Fin (suc n) ] (triangle-number i == n) -> Dec (isTriangleNumber n)
    pos-case v = yes (unsquash (isProp-isTriangleNumber n) (∥-map (\{ ((i , _) , p) -> (i , p) }) v))

    neg-case : (∀ ((i , _) : Fin (suc n)) -> triangle-number i != n) -> Dec (isTriangleNumber n)
    neg-case ne = no neg-case'
      where
      neg-case' : ¬ (isTriangleNumber n)
      neg-case' (i , p) = ne (i , i<n) p
        where
        i<n : i < suc n
        i<n = trans-≤-< (triangle-number-inflationary i) (suc-≤ (path-≤ p))

opaque
  unfolding triangle-number

  isTriangleNumber-zero : isTriangleNumber zero
  isTriangleNumber-zero = zero , refl
