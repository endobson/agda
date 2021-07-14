{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.order where

open import base
open import equality
open import rational
open import rational.order hiding (_<_)
open import real
open import real.arithmetic
open import real.sequence
open import ring.implementations.rational
open import semiring
open import truncation
open import order
open import order.instances.rational

private
  ℝ+ᵉ₁-preserves-< : (a b c : ℝ) -> b ℝ< c -> (a ℝ+ᵉ b) ℝ< (a ℝ+ᵉ c)
  ℝ+ᵉ₁-preserves-< a b c b<c = ∥-bind handle b<c
    where
    Ans = (a ℝ+ᵉ b) ℝ< (a ℝ+ᵉ c)
    module a = Real a
    module b = Real b
    module c = Real c

    handle : b ℝ<' c -> Ans
    handle (q , bu-q , cl-q) = ∥-bind handle2 (b.isLowerOpen-U q bu-q)
      where
      handle2 : Σ[ r ∈ ℚ ] (r < q × b.U r) -> Ans
      handle2 (r , r<q , bu-r) = ∥-bind handle3 (find-open-ball a d⁺)
        where
        d = diffℚ r q
        d⁺ : ℚ⁺
        d⁺ = d , r<q

        handle3 : OpenBall a d -> Ans
        handle3 (s1 , s2 , al-s1 , au-s2 , sd-path) =
          ∣ s2 + r , ∣ (s2 , r , au-s2 , bu-r , refl) ∣ , ∣ s1 , q , al-s1 , cl-q , sum-path ∣ ∣
          where
          sum-path : s1 + q == s2 + r
          sum-path = +-left (sym (diffℚ-step s2 s1) >=>
                             +-right (diffℚ-anticommute s2 s1 >=>
                                      cong r-_ sd-path >=>
                                      sym (diffℚ-anticommute q r))) >=>
                     +-assoc >=>
                     +-right (+-commute >=>
                              diffℚ-step q r)


abstract
  ℝ+₁-preserves-< : (a b c : ℝ) -> b ℝ< c -> (a ℝ+ b) ℝ< (a ℝ+ c)
  ℝ+₁-preserves-< a b c b<c = subst2 _ℝ<_ (sym ℝ+-eval) (sym ℝ+-eval) (ℝ+ᵉ₁-preserves-< a b c b<c)

  ℝ+₂-preserves-< : (a b c : ℝ) -> a ℝ< b -> (a ℝ+ c) ℝ< (b ℝ+ c)
  ℝ+₂-preserves-< a b c lt =
    subst2 _ℝ<_ (ℝ+-commute c a) (ℝ+-commute c b) (ℝ+₁-preserves-< c a b lt)


-- Invertible differences

ℝ#->ℝInv : (x y : ℝ) -> x ℝ# y -> ℝInv (y ℝ+ (ℝ- x))
ℝ#->ℝInv x y (inj-l x<y) = inj-r (subst (_ℝ< (y ℝ+ (ℝ- x))) (ℝ+-inverse x) (ℝ+₂-preserves-< x y (ℝ- x) x<y))
ℝ#->ℝInv x y (inj-r y<x) = inj-l (subst ((y ℝ+ (ℝ- x)) ℝ<_) (ℝ+-inverse x) (ℝ+₂-preserves-< y x (ℝ- x) y<x))
