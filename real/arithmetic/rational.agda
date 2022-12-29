{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.rational where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import rational.proper-interval
open import rational.proper-interval.abs
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.interval
open import real.rational
open import ring.implementations.real
open import semiring
open import truncation


ℚ->ℝ-preserves-+ : {q r : ℚ} -> ℚ->ℝ (q + r) == ℚ->ℝ q + ℚ->ℝ r
ℚ->ℝ-preserves-+ {q} {r} = sym (ℝ∈Iℚ->path _ _ f) >=> sym ℝ+-eval
  where
  module q = Real (ℚ->ℝ q)
  module r = Real (ℚ->ℝ r)
  s = ((ℚ->ℝ q) ℝ+ᵉ (ℚ->ℝ r))
  module s = Real s

  f : (qi : Iℚ) -> ℝ∈Iℚ s qi -> ℝ∈Iℚ (ℚ->ℝ (q + r)) qi
  f qi@(Iℚ-cons l u _) (sL-l , sU-u) =
    unsquash (isProp-ℝ∈Iℚ (ℚ->ℝ (q + r)) qi) (∥-map2 handle sL-l sU-u)
    where
    handle : Σ[ lq ∈ ℚ ] Σ[ lr ∈ ℚ ] (q.L lq × r.L lr × lq + lr == l) ->
             Σ[ uq ∈ ℚ ] Σ[ ur ∈ ℚ ] (q.U uq × r.U ur × uq + ur == u) ->
             ℝ∈Iℚ (ℚ->ℝ (q + r)) qi
    handle (lq , lr , L-lq , L-lr , lq+lr=l) (uq , ur , U-uq , U-ur , uq+ur=u) =
      ℚ<->L (subst2 _<_ lq+lr=l refl (+-preserves-< (L->ℚ< L-lq) (L->ℚ< L-lr))) ,
      ℚ<->U (subst2 _<_ refl uq+ur=u (+-preserves-< (U->ℚ< U-uq) (U->ℚ< U-ur)))

ℚ->ℝ-preserves-- : {q : ℚ} -> ℚ->ℝ (- q) == - (ℚ->ℝ q)
ℚ->ℝ-preserves-- {q} = sym (ℝ∈Iℚ->path _ _ f) >=> sym ℝ--eval
  where
  f : (qi : Iℚ) -> ℝ∈Iℚ (ℝ-ᵉ (ℚ->ℝ q)) qi -> ℝ∈Iℚ (ℚ->ℝ (- q)) qi
  f (Iℚ-cons l u _) (U-ml , L-mu) = L-case , U-case
    where
    L-case : Real.L (ℚ->ℝ (- q)) l
    L-case = ℚ<->L (subst2 _<_ minus-double-inverse refl (minus-flips-< (U->ℚ< U-ml)))
    U-case : Real.U (ℚ->ℝ (- q)) u
    U-case = ℚ<->U (subst2 _<_ refl minus-double-inverse (minus-flips-< (L->ℚ< L-mu)))

ℚ->ℝ-preserves-diff : {q r : ℚ} -> ℚ->ℝ (diff q r) == diff (ℚ->ℝ q) (ℚ->ℝ r)
ℚ->ℝ-preserves-diff =
  ℚ->ℝ-preserves-+ >=> +-right ℚ->ℝ-preserves--


private
  ℝ∈Iℚ->ℚ∈Iℚ : {q : ℚ} (qi : Iℚ) -> ℝ∈Iℚ (ℚ->ℝ q) qi -> ℚ∈Iℚ q qi
  ℝ∈Iℚ->ℚ∈Iℚ qi (L , U) = weaken-< (L->ℚ< L) , weaken-< (U->ℚ< U)

  ℚ∈Iℚ->ℝ∈Iℚ : {q : ℚ} {a b : Iℚ} -> a i⊂ b -> ℚ∈Iℚ q a -> ℝ∈Iℚ (ℚ->ℝ q) b
  ℚ∈Iℚ->ℝ∈Iℚ (i⊂-cons bl<al au<bu) (al≤q , q≤au) =
    ℚ<->L (trans-<-≤ bl<al al≤q) ,
    ℚ<->U (trans-≤-< q≤au au<bu)

ℚ->ℝ-preserves-* : {q r : ℚ} -> ℚ->ℝ (q * r) == ℚ->ℝ q * ℚ->ℝ r
ℚ->ℝ-preserves-* {q} {r} = sym (ℝ∈Iℚ->path _ _ f)
  where
  q' = ℚ->ℝ q
  r' = ℚ->ℝ r
  qr' = ℚ->ℝ (q * r)
  f : (qi : Iℚ) -> ℝ∈Iℚ (q' * r') qi -> ℝ∈Iℚ qr' qi
  f qi@(Iℚ-cons l u _) q*r∈qi =
    unsquash (isProp-ℝ∈Iℚ qr' qi) (∥-bind handle (tighter-ℝ∈Iℚ (q' * r') qi q*r∈qi))
    where
    handle : Σ[ a ∈ Iℚ ] ((a i⊂ qi) × ℝ∈Iℚ (q' * r') a) ->
             ∥ ℝ∈Iℚ qr' qi ∥
    handle (a , a⊂qi , q*r∈a) = (∥-map handle2 (ℝ∈Iℚ-*⁻ q' r' a q*r∈a))
      where
      handle2 : Σ[ b ∈ Iℚ ] Σ[ c ∈ Iℚ ] (ℝ∈Iℚ q' b × ℝ∈Iℚ r' c × (b i* c) i⊆ a) ->
               ℝ∈Iℚ qr' qi
      handle2 (b , c , q'∈b , r'∈c , bc⊆a) = ℚ∈Iℚ->ℝ∈Iℚ (trans-i⊆-i⊂ bc⊆a a⊂qi) qr∈bc
        where
        q∈b = ℝ∈Iℚ->ℚ∈Iℚ b q'∈b
        r∈c = ℝ∈Iℚ->ℚ∈Iℚ c r'∈c
        qr∈bc = ℚ∈Iℚ-* q r b c q∈b r∈c

-- 1/2. Usefule now that we have shown that ℚ->ℝ-preserves-+
1/2ℝ : ℝ
1/2ℝ = ℚ->ℝ 1/2r

1/2ℝ-1-path : 1/2ℝ + 1/2ℝ == 1#
1/2ℝ-1-path =
  sym ℚ->ℝ-preserves-+ >=>
  cong ℚ->ℝ (+-cong (sym *-right-one) (sym *-right-one) >=> 1/2r-path' 1#)

0<1/2ℝ : 0# < 1/2ℝ
0<1/2ℝ = ℚ->ℝ-preserves-< _ _ Pos-1/2r
