{-# OPTIONS --cubical --safe --exact-split #-}

module real.distance where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import metric-space
open import metric-space.instances.real
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import real
open import real.subspace
open import relation
open import subset.subspace
open import truncation

opaque
  split-distance<ε : (x y : ℝ) ((ε , _) : ℝ⁺) -> ∥ Tri⊎ (y < x) (distance x y < ε) (x < y) ∥
  split-distance<ε x y (ε , 0<ε) =
    ∥-map2 handle (comparison-< 0# (diff x y) ε 0<ε) (comparison-< 0# (diff y x) ε 0<ε)
    where
    handle : 0# < (diff x y) ⊎ (diff x y) < ε -> 0# < (diff y x) ⊎ (diff y x) < ε ->
             Tri⊎ (y < x) (distance x y < ε) (x < y)
    handle (inj-l 0<dxy) _             = tri⊎-> (diff-0<⁻ 0<dxy)
    handle (inj-r dxy<ε) (inj-l 0<dyx) = tri⊎-< (diff-0<⁻ 0<dyx)
    handle (inj-r dxy<ε) (inj-r dyx<ε) =
      tri⊎-= (max-least-< dxy<ε (trans-=-< (sym diff-anticommute) dyx<ε))

  distance-diff-<₁ : {a b c : ℝ} -> distance a b < diff a c -> b < c
  distance-diff-<₁{a} {b} {c} dist-ab<diff-ac = diff-0<⁻ 0<diff-bc
    where
    diff-ab<diff-ac : diff a b < diff a c
    diff-ab<diff-ac = trans-≤-< max-≤-left dist-ab<diff-ac

    0<diff-bc : 0# < diff b c
    0<diff-bc =
      subst2 _<_ (diff-trans >=> +-inverse) diff-trans (+₁-preserves-< diff-ab<diff-ac)

  distance-diff-<₂ : {a b c : ℝ} -> distance a b < diff c b -> c < a
  distance-diff-<₂ {a} {b} {c} dist-ab<diff-cb = diff-0<⁻ 0<diff-ca
    where
    diff-ab<diff-cb : diff a b < diff c b
    diff-ab<diff-cb = trans-≤-< max-≤-left dist-ab<diff-cb

    0<diff-ca : 0# < diff c a
    0<diff-ca =
      subst2 _<_ (diff-trans >=> +-inverse) diff-trans (+₂-preserves-< diff-ab<diff-cb)

  distance-+-swap : {a b c d : ℝ} -> distance (a + b) (c + d) ≤ (distance a c + distance b d)
  distance-+-swap {a} {b} {c} {d} =
    trans-≤-= (distance-triangleᵉ (a + b) (c + b) (c + d)) (+-cong d1 d2)
    where
    d1 : distance (a + b) (c + b) == distance a c
    d1 = cong abs (sym (+₂-preserves-diff))
    d2 : distance (c + b) (c + d) == distance b d
    d2 = cong abs (sym (+₁-preserves-diff))
