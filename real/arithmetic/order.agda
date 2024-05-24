{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.order where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import rational
open import rational.proper-interval
open import rational.order
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.interval
open import real.order
open import real.rational
open import real.sequence
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import truncation
open import order
open import order.instances.rational
open import order.instances.real

private
  ℝ+ᵉ₁-preserves-< : (a b c : ℝ) -> b ℝ< c -> (a ℝ+ᵉ b) ℝ< (a ℝ+ᵉ c)
  ℝ+ᵉ₁-preserves-< a b c b<c = ∥-bind handle b<c
    where
    Ans = (a ℝ+ᵉ b) ℝ< (a ℝ+ᵉ c)
    module a = Real a
    module b = Real b
    module c = Real c

    handle : b ℝ<' c -> Ans
    handle (ℝ<'-cons q bu-q cl-q) = ∥-bind handle2 (b.isLowerOpen-U q bu-q)
      where
      handle2 : Σ[ r ∈ ℚ ] (r < q × b.U r) -> Ans
      handle2 (r , r<q , bu-r) = ∥-bind handle3 (find-open-ball a d⁺)
        where
        d = diff r q
        d⁺ : ℚ⁺
        d⁺ = d , Pos-diffℚ r q r<q

        handle3 : OpenBall a d -> Ans
        handle3 (s1 , s2 , al-s1 , au-s2 , sd-path) =
          ∣ ℝ<'-cons (s2 + r)  (∣ (s2 , r , au-s2 , bu-r , refl) ∣)
                               (∣ s1 , q , al-s1 , cl-q , sum-path ∣) ∣
          where
          sum-path : s1 + q == s2 + r
          sum-path = +-left (sym diff-step >=>
                             +-right (diff-anticommute >=>
                                      cong r-_ sd-path >=>
                                      sym diff-anticommute)) >=>
                     +-assoc >=>
                     +-right (+-commute >=>
                              diff-step)


abstract
  ℝ+₁-preserves-< : (a b c : ℝ) -> b ℝ< c -> (a ℝ+ b) ℝ< (a ℝ+ c)
  ℝ+₁-preserves-< a b c b<c = subst2 _ℝ<_ (sym ℝ+-eval) (sym ℝ+-eval) (ℝ+ᵉ₁-preserves-< a b c b<c)

  ℝ+₂-preserves-< : (a b c : ℝ) -> a ℝ< b -> (a ℝ+ c) ℝ< (b ℝ+ c)
  ℝ+₂-preserves-< a b c lt =
    subst2 _ℝ<_ (ℝ+-commute c a) (ℝ+-commute c b) (ℝ+₁-preserves-< c a b lt)

private
  ℝ*ᵉ-preserves-0< : (a b : ℝ) -> 0ℝ ℝ< a -> 0ℝ ℝ< b -> 0ℝ ℝ< (a ℝ*ᵉ b)
  ℝ*ᵉ-preserves-0< a b 0<a 0<b = (∥-map2 handle (ℝ∈Iℚ-Pos a 0<a) (ℝ∈Iℚ-Pos b 0<b))
    where
    al-0 = ℝ<->L 0<a
    bl-0 = ℝ<->L 0<b
    handle : Σ[ ia ∈ Iℚ ] (ℝ∈Iℚ a ia × PosI ia) -> Σ[ ib ∈ Iℚ ] (ℝ∈Iℚ b ib × PosI ib) ->
             0ℝ ℝ<' (a ℝ*ᵉ b)
    handle (ia , a∈ia , pos-ia) (ib , b∈ib , pos-ib) =
      ℝ<'-cons l (ℚ<->U 0<l) (∣ ia , ib , a∈ia , b∈ib , subst (\x -> i-Lower x l) iab-path refl-ℚ≤ ∣)
      where
      iab = ia i* ib
      iab' = i*-NN ia ib (weaken-< pos-ia) (weaken-< pos-ib)
      iab-path = i*-NN-path ia ib (weaken-< pos-ia) (weaken-< pos-ib)

      l = Iℚ.l iab'
      pos-l = r*-preserves-Pos _ _ pos-ia pos-ib
      0<l = Pos-0< l pos-l

abstract
  ℝ*-preserves-0< : (a b : ℝ) -> 0ℝ ℝ< a -> 0ℝ ℝ< b -> 0ℝ ℝ< (a ℝ* b)
  ℝ*-preserves-0< a b 0<a 0<b = subst (0ℝ ℝ<_) (sym ℝ*-eval) (ℝ*ᵉ-preserves-0< a b 0<a 0<b)

  ℝ*₁-preserves-< : (a b c : ℝ) -> 0ℝ ℝ< a -> (b ℝ< c) -> (a ℝ* b) ℝ< (a ℝ* c)
  ℝ*₁-preserves-< a b c 0<a b<c = ab<ac
    where
    module _ where
      0<cb : 0# < (c + (- b))
      0<cb = subst2 _<_ +-inverse refl (ℝ+₂-preserves-< _ _ _ b<c)

      0<acb : 0# < (a ℝ* (c + (- b)))
      0<acb = ℝ*-preserves-0< _ _ 0<a 0<cb

      ab+acb=ac : (a ℝ* b) + (a ℝ* (c + (- b))) == a ℝ* c
      ab+acb=ac =
        sym *-distrib-+-left >=>
        *-right (+-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero)

      ab<ac : (a * b) < (a * c)
      ab<ac = subst2 _<_ +-right-zero ab+acb=ac (ℝ+₁-preserves-< _ _ _ 0<acb)


-- Invertible differences

ℝ#->ℝInv : (x y : ℝ) -> x # y -> ℝInv (y ℝ+ (ℝ- x))
ℝ#->ℝInv x y (inj-l x<y) = inj-r (subst (_< (y ℝ+ (ℝ- x))) (ℝ+-inverse x) (ℝ+₂-preserves-< x y (ℝ- x) x<y))
ℝ#->ℝInv x y (inj-r y<x) = inj-l (subst ((y ℝ+ (ℝ- x)) <_) (ℝ+-inverse x) (ℝ+₂-preserves-< y x (ℝ- x) y<x))
