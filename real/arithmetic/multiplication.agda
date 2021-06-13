{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.factor-order
open import real
open import real.sequence
open import relation hiding (U)
open import truncation

module _ (x y : ℝ)
  (upperOpenℚ⁻ : (z : ℝ) -> (q : ℚ⁻) -> (Real.L z ⟨ q ⟩) ->
                 ∃[ r ∈ ℚ⁻ ] (⟨ q ⟩ < ⟨ r ⟩ × Real.L z ⟨ r ⟩))
  (lowerOpenℚ⁻ : (z : ℝ) -> (q : ℚ⁻) -> (Real.U z ⟨ q ⟩) ->
                 ∃[ r ∈ ℚ⁻ ] (⟨ r ⟩ < ⟨ q ⟩ × Real.U z ⟨ r ⟩))
  (refl-ℚ≤ : (q : ℚ) -> q ℚ≤ q)
  (weaken-ℚ< : {q r : ℚ} -> q < r -> q ℚ≤ r)
  (sqrt-ℚ< : (q : ℚ⁺) -> ∃[ r ∈ ℚ⁺ ] ((⟨ r ⟩ r* ⟨ r ⟩) < ⟨ q ⟩))
  where
  private
    module x = Real x
    module y = Real y

    data L' : (q : ℚ) -> Type₀ where
      L'-pp : (q1 : ℚ⁺) (q2 : ℚ⁺) -> x.L ⟨ q1 ⟩ -> y.L ⟨ q2 ⟩ -> L' (⟨ q1 ⟩ r* ⟨ q2 ⟩)
      L'-nn : (q1 : ℚ⁻) (q2 : ℚ⁻) -> x.U ⟨ q1 ⟩ -> y.U ⟨ q2 ⟩ -> L' (⟨ q1 ⟩ r* ⟨ q2 ⟩)
      L'-pn : (q1 : ℚ⁺) (q2 : ℚ⁻) -> x.U ⟨ q1 ⟩ -> y.L ⟨ q2 ⟩ -> L' (⟨ q1 ⟩ r* ⟨ q2 ⟩)
      L'-np : (q1 : ℚ⁻) (q2 : ℚ⁺) -> x.L ⟨ q1 ⟩ -> y.U ⟨ q2 ⟩ -> L' (⟨ q1 ⟩ r* ⟨ q2 ⟩)
      L'-<  : (q1 q2 : ℚ) -> (q1 < q2) -> L' q2 -> L' q1

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥


    U' : Pred ℚ ℓ-zero
    U' q = Σ[ r ∈ ℚ ] (r < q × (Comp L r))
    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥


    Inhabited-L : ∃ ℚ L
    Inhabited-L = ∥-map2 handle (ℝ->Pos-U x) (ℝ->Neg-L y)
      where
      handle : Σ[ q1 ∈ ℚ⁺ ] (x.U ⟨ q1 ⟩) -> Σ[ q2 ∈ ℚ⁻ ] (y.L ⟨ q2 ⟩) -> Σ ℚ L
      handle (q1 , xu-q1) (q2 , yl-q2) = _ , ∣ L'-pn q1 q2 xu-q1 yl-q2 ∣

    isLowerSet-L : isLowerSet L
    isLowerSet-L q r q<r = ∥-map (L'-< q r q<r)


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      Res' = Σ[ r ∈ ℚ ] (q < r × L r)
      Res  = ∥ Res' ∥

      handle : L' q -> Res
      handle (L'-< _ r q<r lr) = ∣ r , q<r , ∣ lr ∣ ∣
      handle (L'-pp (r1 , pos-r1) r2⁺@(r2 , _) xl-r1 yl-r2) =
        ∥-map handle2 (x.isUpperOpen-L r1 xl-r1)
        where
        handle2 : Σ[ r3 ∈ ℚ ] (r1 < r3 × x.L r3) -> Res'
        handle2 (r3 , r1<r3 , xl-r3) =
          _ , r*₂-preserves-order r1 r3 r2⁺ r1<r3 , ∣ L'-pp r3⁺ r2⁺ xl-r3 yl-r2 ∣
          where
          r3⁺ : ℚ⁺
          r3⁺ = r3 , subst Posℚ (r+-right-zero r3)
                           (trans-< {_} {_} {_} {0r} {r1} {r3} (Pos-0< _ pos-r1) r1<r3)
      handle (L'-np r1⁻@(r1 , _) r2⁺@(r2 , _) xl-r1 yu-r2) =
        ∥-map handle2 (upperOpenℚ⁻ x r1⁻ xl-r1)
        where
        handle2 : Σ[ r3 ∈ ℚ⁻ ] (r1 < ⟨ r3 ⟩ × x.L ⟨ r3 ⟩) -> Res'
        handle2 (r3⁻@(r3 , _) , r1<r3 , xl-r3) =
          _ , r*₂-preserves-order r1 r3 r2⁺ r1<r3 , ∣ L'-np r3⁻ r2⁺ xl-r3 yu-r2 ∣
      handle (L'-pn r1⁺@(r1 , _) r2⁻@(r2 , _) xu-r1 yl-r2) =
        ∥-map handle2 (upperOpenℚ⁻ y r2⁻ yl-r2)
        where
        handle2 : Σ[ r3 ∈ ℚ⁻ ] (r2 < ⟨ r3 ⟩ × y.L ⟨ r3 ⟩) -> Res'
        handle2 (r3⁻@(r3 , _) , r2<r3 , yl-r3) =
          _ , r*₁-preserves-order r1⁺ r2 r3 r2<r3 , ∣ L'-pn r1⁺ r3⁻ xu-r1 yl-r3 ∣
      handle (L'-nn r1⁻@(r1 , _) r2⁻@(r2 , _) xu-r1 yu-r2) =
        ∥-map handle2 (lowerOpenℚ⁻ y r2⁻ yu-r2)
        where
        handle2 : Σ[ r3 ∈ ℚ⁻ ] (⟨ r3 ⟩ < r2 × y.U ⟨ r3 ⟩) -> Res'
        handle2 (r3⁻@(r3 , _) , r3<r2 , yu-r3) =
          _ , r*₁-flips-order r1⁻ r3 r2 r3<r2 , ∣ L'-nn r1⁻ r3⁻ xu-r1 yu-r3 ∣


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q1 = ∥-map handle
      where
      handle : U' q1 -> Σ[ q2 ∈ ℚ ] (q2 < q1 × U q2)
      handle (r , r<q1 , ur) = (midℚ r q1 , midℚ-<₂ r q1 r<q1 , ∣ (r , midℚ-<₁ r q1 r<q1 , ur) ∣)


    isUpperSet-U : isUpperSet U
    isUpperSet-U q r q<r = ∥-map handle
      where
      handle : U' q -> U' r
      handle (s , s<q , ¬ls) = (s , trans-< {_} {_} {_} {s} {q} {r} s<q q<r , ¬ls)

    disjoint : Universal (Comp (L ∩ U))
    disjoint q (lq , uq) = unsquash isPropBot (∥-map handle uq)
      where
      handle : U' q -> Bot
      handle (r , r<q , ¬lr) = ¬lr (isLowerSet-L r q r<q lq)

--    located : (q r : ℚ) -> (q < r) -> ∥ L q ⊎ U r ∥
--    located q r q<r = ∥-bind2 handle (find-open-ball x ε⁺) (find-open-ball y ε⁺)
--      where
--      ε : ℚ
--      ε = ?
--      ε⁺ : ℚ⁺
--      ε⁺ = ε , ?
--
--      Ans = ∥ L q ⊎ U r ∥
--      handle : OpenBall x ε -> OpenBall y ε -> Ans
--      handle (a , b , lx-a , ux-b , ab-path) (c , d , ly-c , uy-d , cd-path) =
--        handle2 (split-< a 0r)
--        where
--        handle2 : (a < 0r ⊎ 0r ≤ a) -> Ans
--        handle2 = ?

  module _
    (Inhabited-U : Inhabited U)
    (located : (q r : ℚ) -> (q < r) -> ∥ L q ⊎ U r ∥)
    where
    _ℝ*_ : ℝ
    _ℝ*_ = record
      { L = L
      ; U = U
      ; isProp-L = \q -> squash
      ; isProp-U = \q -> squash
      ; Inhabited-L = Inhabited-L
      ; Inhabited-U = Inhabited-U
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; disjoint = disjoint
      ; located = located
      }
