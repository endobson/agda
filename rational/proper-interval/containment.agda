{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.containment where

open import additive-group
open import base
open import equality
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.proper-interval
open import relation
open import semiring

ℚ∈Iℚ-i∪₁ : (q : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q (a i∪ b)
ℚ∈Iℚ-i∪₁ _ _ _ (al≤q , q≤au) = trans-≤ min-≤-left al≤q , trans-≤ q≤au max-≤-left

ℚ∈Iℚ-i∪₂ : (q : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q b -> ℚ∈Iℚ q (a i∪ b)
ℚ∈Iℚ-i∪₂ q a b q∈b = subst (ℚ∈Iℚ q) (i∪-commute b a) (ℚ∈Iℚ-i∪₁ q b a q∈b)

ℚ∈Iℚ-i-scale : (k q : ℚ) (a : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ (k * q) (i-scale k a)
ℚ∈Iℚ-i-scale k q a@(Iℚ-cons l u l≤u) (l≤q , q≤u) = handle (split-< k 0#)
  where
  handle : (k < 0# ⊎ 0# ≤ k) -> ℚ∈Iℚ (k * q) (i-scale k a)
  handle (inj-l k<0) = subst (ℚ∈Iℚ (k * q)) (i-scale-≤0-path (k , k≤0) a) kq∈ka'
    where
    k≤0 = weaken-< k<0
    kq∈ka' : ℚ∈Iℚ (k * q) (i-scale-≤0 (k , k≤0) a)
    kq∈ka' = *₁-flips-≤ k≤0 q≤u , *₁-flips-≤ k≤0 l≤q

  handle (inj-r 0≤k) = subst (ℚ∈Iℚ (k * q)) (i-scale-0≤-path (k , 0≤k) a) kq∈ka'
    where
    kq∈ka' : ℚ∈Iℚ (k * q) (i-scale-0≤ (k , 0≤k) a)
    kq∈ka' = *₁-preserves-≤ 0≤k l≤q , *₁-preserves-≤ 0≤k q≤u

ℚ∈Iℚ-⊆ : (q : ℚ) -> {a b : Iℚ} -> (a i⊆ b) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q b
ℚ∈Iℚ-⊆ q {_} {b} (i⊆-cons bl≤al au≤bu) (al≤q , q≤au) =
  trans-≤ bl≤al al≤q , trans-≤ q≤au au≤bu

ℚ∈Iℚ-* : {q r : ℚ} (a b : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ r b -> ℚ∈Iℚ (q * r) (a i* b)
ℚ∈Iℚ-* {q} {r} a@(Iℚ-cons al au al≤au) b q∈a r∈b =
  subst ∈ab *-commute rq∈ab
  where
  ab = (a i* b)
  abl = Iℚ.l ab
  abu = Iℚ.u ab

  ∈ab : Pred ℚ ℓ-zero
  ∈ab q = ℚ∈Iℚ q ab


  alr∈alb : ℚ∈Iℚ (al * r) (i-scale al b)
  alr∈alb = ℚ∈Iℚ-i-scale al r b r∈b

  alr∈ab : ℚ∈Iℚ (al * r) ab
  alr∈ab = ℚ∈Iℚ-i∪₁ (al * r) (i-scale al b) (i-scale au b) alr∈alb

  ral∈ab : ℚ∈Iℚ (r * al) ab
  ral∈ab = subst ∈ab *-commute alr∈ab

  aur∈aub : ℚ∈Iℚ (au * r) (i-scale au b)
  aur∈aub = ℚ∈Iℚ-i-scale au r b r∈b

  aur∈ab : ℚ∈Iℚ (au * r) ab
  aur∈ab = ℚ∈Iℚ-i∪₂ (au * r) (i-scale al b) (i-scale au b) aur∈aub

  rau∈ab : ℚ∈Iℚ (r * au) ab
  rau∈ab = subst ∈ab *-commute aur∈ab

  ra⊆ab : i-scale r a i⊆ ab
  ra⊆ab = i⊆-cons (min-property {P = abl ≤_} (r * al) (r * au) (fst ral∈ab) (fst rau∈ab))
                  (max-property {P = _≤ abu} (r * al) (r * au) (snd ral∈ab) (snd rau∈ab))

  rq∈ra : ℚ∈Iℚ (r * q) (i-scale r a)
  rq∈ra = ℚ∈Iℚ-i-scale r q a q∈a

  rq∈ab : ℚ∈Iℚ (r * q) ab
  rq∈ab = ℚ∈Iℚ-⊆ (r * q) ra⊆ab rq∈ra


ℚ∈Iℚ-l : (a : Iℚ) -> (ℚ∈Iℚ (Iℚ.l a) a)
ℚ∈Iℚ-l (Iℚ-cons l u l≤u) = refl-≤ , l≤u

ℚ∈Iℚ-u : (a : Iℚ) -> (ℚ∈Iℚ (Iℚ.u a) a)
ℚ∈Iℚ-u (Iℚ-cons l u l≤u) = l≤u , refl-≤
