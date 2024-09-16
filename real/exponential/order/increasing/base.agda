{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.order.increasing.base where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import fin
open import finset.instances
open import finsum.order
open import functions
open import funext
open import heyting-field.instances.real
open import nat
open import order
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.exponentiation
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.exponential-series
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.order
open import ring.implementations.real
open import semiring
open import sequence.partial-sums

opaque
  exp-0≤-preserves-< : {x y : ℝ} -> 0# ≤ x -> x < y -> exp x < exp y
  exp-0≤-preserves-< {x} {y} 0≤x x<y = exp-x<exp-y
    where
    p1 : ∀ {x} i -> (partial-sums (exp-terms x) (suc (suc i))) ==
                    (exp-terms x 0 + exp-terms x 1) +
                    (partial-sums (exp-terms x ∘ suc ∘ suc) i)
    p1 i =
      partial-sums-suc >=>
      +-right partial-sums-suc >=>
      sym +-assoc

    p2 : ∀ {x} i -> (partial-sums (exp-terms x ∘ suc ∘ suc) i) ==
                    diff (1# + x) (partial-sums (exp-terms x) (suc (suc i)))
    p2 i =
      sym +-right-zero >=>
      +-right (sym +-inverse) >=>
      sym +-assoc >=>
      +-left (sym (p1 i >=> +-left (+-cong exp-term0 exp-term1) >=> +-commute))

    1+x<1+y : (1# + x) < (1# + y)
    1+x<1+y = +₁-preserves-< x<y

    isLimit-drop2x : isLimit (partial-sums (exp-terms x) ∘ suc ∘ suc) (exp x)
    isLimit-drop2x = dropN-preserves-limit (isLimit-exp x)
    isLimit-drop2y : isLimit (partial-sums (exp-terms y) ∘ suc ∘ suc) (exp y)
    isLimit-drop2y = dropN-preserves-limit (isLimit-exp y)

    px : ℝ
    px = diff (1# + x) (exp x)
    py : ℝ
    py = diff (1# + y) (exp y)

    isLimit-px : isLimit (partial-sums (exp-terms x ∘ suc ∘ suc)) px
    isLimit-px =
      subst2 isLimit (funExt (\i -> sym (p2 i))) refl
        (diff-preserves-limit (isLimit-constant-seq (1# + x)) isLimit-drop2x)
    isLimit-py : isLimit (partial-sums (exp-terms y ∘ suc ∘ suc)) py
    isLimit-py =
      subst2 isLimit (funExt (\i -> sym (p2 i))) refl
        (diff-preserves-limit (isLimit-constant-seq (1# + y)) isLimit-drop2y)

    pxs<pys : ∀ i -> (partial-sums (exp-terms x ∘ suc ∘ suc) i) ≤
                     (partial-sums (exp-terms y ∘ suc ∘ suc) i)
    pxs<pys n =
      finiteSum-preserves-≤ txs≤tys
      where
      txs≤tys : ∀ ((i , _) : Fin n) -> exp-terms x (suc (suc i)) ≤ exp-terms y (suc (suc i))
      txs≤tys (i , _) =
        *₁-preserves-≤ (weaken-< (0<1/ℕ _))
          (^ℕ-0≤-preserves-≤ 0≤x (suc (suc i)) (weaken-< x<y))

    px≤py : px ≤ py
    px≤py = isLimit-preserves-≤ isLimit-px isLimit-py pxs<pys

    exp-x<exp-y : exp x < exp y
    exp-x<exp-y =
      subst2 _<_ diff-step diff-step
        (trans-<-≤ (+₂-preserves-< 1+x<1+y) (+₁-preserves-≤ px≤py))

  exp-abs-≤ : {x : ℝ} -> exp x ≤ exp (abs x)
  exp-abs-≤ {x} = isLimit-preserves-≤ (isLimit-exp x) (isLimit-exp (abs x)) seq≤
    where
    term≤ : (i : ℕ) -> (exp-terms x i) ≤ (exp-terms (abs x) i)
    term≤ i = *₁-preserves-≤ (weaken-< (0<1/ℕ _)) (trans-≤-= abs-≤ (abs-^ℕ-path i))

    seq≤ : (i : ℕ) -> partial-sums (exp-terms x) i ≤ partial-sums (exp-terms (abs x)) i
    seq≤ i = finiteSum-preserves-≤ (\(i , _) -> term≤ i)
