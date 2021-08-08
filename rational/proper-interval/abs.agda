{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.abs where

open import base
open import equality
open import order
open import order.instances.rational
open import ordered-ring
open import ordered-semiring.instances.rational
open import rational
open import rational.minmax
open import rational.order
open import rational.proper-interval
open import rational.proper-interval.maxabs-multiplication
open import relation
open import ring
open import ring.implementations.rational
open import semiring
open import sign
open import sign.instances.rational


ImbalancedI : Pred Iℚ ℓ-zero
ImbalancedI (Iℚ-cons l u _) = (- l) ℚ≤ u


i-maxabs≤->ImbalancedI : (a : Iℚ) -> (i-maxabs a ℚ≤ Iℚ.u a) -> ImbalancedI a
i-maxabs≤->ImbalancedI (Iℚ-cons l u l≤u) ma≤au =
  trans-ℚ≤ { - l}
    (maxℚ-≤-right l (- l))
    (trans-ℚ≤ {absℚ l} (maxℚ-≤-left (absℚ l) (absℚ u)) ma≤au)

ImbalancedI->i-maxabs : (a : Iℚ) -> ImbalancedI a -> (i-maxabs a == Iℚ.u a)
ImbalancedI->i-maxabs (Iℚ-cons l u l≤u) -l≤u =
  maxℚ-right (absℚ l) (absℚ u) al≤au >=> au=u
  where
  al≤u : absℚ l ℚ≤ u
  al≤u = maxℚ-property {P = _ℚ≤ u} l (- l) l≤u -l≤u

  nn-u : NonNeg u
  nn-u = NonNeg-≤ (absℚ l) u (NonNeg-absℚ l) al≤u

  au=u : absℚ u == u
  au=u = (absℚ-NonNeg nn-u)

  al≤au : absℚ l ℚ≤ absℚ u
  al≤au = trans-ℚ≤ {absℚ l} al≤u (maxℚ-≤-left u (- u))


ℚ∈Iℚ-i∪₁ : (q : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q (a i∪ b)
ℚ∈Iℚ-i∪₁ q (Iℚ-cons al au _) (Iℚ-cons bl bu _) (al≤q , q≤au) =
  trans-ℚ≤ {minℚ al bl} (minℚ-≤-left al bl) al≤q ,
  trans-ℚ≤ {q} q≤au (maxℚ-≤-left au bu)

ℚ∈Iℚ-i∪₂ : (q : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q b -> ℚ∈Iℚ q (a i∪ b)
ℚ∈Iℚ-i∪₂ q a b q∈b = subst (ℚ∈Iℚ q) (i∪-commute b a) (ℚ∈Iℚ-i∪₁ q b a q∈b)

ℚ∈Iℚ-i-scale : (k q : ℚ) (a : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ (k * q) (i-scale k a)
ℚ∈Iℚ-i-scale k q a@(Iℚ-cons l u l≤u) (l≤q , q≤u) = handle (split-< k 0r)
  where
  handle : (k < 0r ⊎ 0r ℚ≤ k) -> ℚ∈Iℚ (k * q) (i-scale k a)
  handle (inj-l k<0) = subst (ℚ∈Iℚ (k * q)) (i-scale-NP-path (k , np-k) a) kq∈ka'
    where
    np-k : NonPos k
    np-k = ≤0-NonPos k (weaken-< k<0)

    kq∈ka' : ℚ∈Iℚ (k * q) (i-scale-NP (k , np-k) a)
    kq∈ka' = *₁-flips-≤ k q u (weaken-< k<0) q≤u ,
             *₁-flips-≤ k l q (weaken-< k<0) l≤q

  handle (inj-r 0≤k) = subst (ℚ∈Iℚ (k * q)) (i-scale-NN-path (k , nn-k) a) kq∈ka'
    where
    nn-k : NonNeg k
    nn-k = 0≤-NonNeg k 0≤k

    kq∈ka' : ℚ∈Iℚ (k * q) (i-scale-NN (k , nn-k) a)
    kq∈ka' = *₁-preserves-≤ k l q 0≤k l≤q ,
             *₁-preserves-≤ k q u 0≤k q≤u

ℚ∈Iℚ-⊆ : (q : ℚ) -> {a b : Iℚ} -> (a i⊆ b) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q b
ℚ∈Iℚ-⊆ q {_} {b} (i⊆-cons bl≤al au≤bu) (al≤q , q≤au) =
  trans-ℚ≤ {Iℚ.l b} bl≤al al≤q , trans-ℚ≤ {q} q≤au au≤bu

ℚ∈Iℚ-* : (q r : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ r b -> ℚ∈Iℚ (q * r) (a i* b)
ℚ∈Iℚ-* q r a@(Iℚ-cons al au al≤au) b q∈a r∈b =
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
  ra⊆ab = i⊆-cons (minℚ-property {P = abl ℚ≤_} (r * al) (r * au) (fst ral∈ab) (fst rau∈ab))
                  (maxℚ-property {P = _ℚ≤ abu} (r * al) (r * au) (snd ral∈ab) (snd rau∈ab))

  rq∈ra : ℚ∈Iℚ (r * q) (i-scale r a)
  rq∈ra = ℚ∈Iℚ-i-scale r q a q∈a

  rq∈ab : ℚ∈Iℚ (r * q) ab
  rq∈ab = ℚ∈Iℚ-⊆ (r * q) ra⊆ab rq∈ra





ℚ∈Iℚ-l : (a : Iℚ) -> (ℚ∈Iℚ (Iℚ.l a) a)
ℚ∈Iℚ-l (Iℚ-cons l u l≤u) = refl-ℚ≤ , l≤u

ℚ∈Iℚ-u : (a : Iℚ) -> (ℚ∈Iℚ (Iℚ.u a) a)
ℚ∈Iℚ-u (Iℚ-cons l u l≤u) = l≤u , refl-ℚ≤

i*-preserves-ImbalancedI : (a b : Iℚ) -> ImbalancedI a -> ImbalancedI b -> ImbalancedI (a i* b)
i*-preserves-ImbalancedI a b imb-a imb-b = i-maxabs≤->ImbalancedI ab mab≤abu
  where
  ab = a i* b
  ma = i-maxabs a
  mb = i-maxabs b
  mab = i-maxabs ab
  au = Iℚ.u a
  bu = Iℚ.u b
  abu = Iℚ.u ab

  aubu≤abu : (au * bu) ℚ≤ abu
  aubu≤abu = snd (ℚ∈Iℚ-* au bu a b (ℚ∈Iℚ-u a) (ℚ∈Iℚ-u b))


  ma=au : ma == au
  ma=au = ImbalancedI->i-maxabs a imb-a

  mb=bu : mb == bu
  mb=bu = ImbalancedI->i-maxabs b imb-b

  mab=aubu : mab == (au * bu)
  mab=aubu = i-maxabs-i* a b >=> *-cong ma=au mb=bu

  mab≤abu : mab ℚ≤ abu
  mab≤abu = subst (_ℚ≤ abu) (sym mab=aubu) aubu≤abu


i-abs : Iℚ -> Iℚ
i-abs (Iℚ-cons l u l≤u) = (Iℚ-cons (maxℚ l 0r) (maxℚ (- l) u) lt)
  where
  LT = (maxℚ l 0r) ℚ≤ (maxℚ (- l) u)
  abstract
    lt : LT
    lt = handle (split-< l 0r)
      where
      handle : (l < 0r) ⊎ (0r ℚ≤ l) -> LT
      handle (inj-l l<0) =
        subst (_ℚ≤ (maxℚ (- l) u))
          (sym (maxℚ-right l 0r (weaken-< l<0)))
          (trans-ℚ≤ {0r} (weaken-< (minus-flips-< l 0r l<0)) (maxℚ-≤-left (- l) u))
      handle (inj-r 0≤l) =
        subst2 (_ℚ≤_) (sym (maxℚ-left l 0r 0≤l)) (sym (maxℚ-right (- l) u -l≤u)) l≤u
        where
        -l≤0 : (- l) ℚ≤ 0r
        -l≤0 = (minus-flips-≤ 0r l 0≤l)
        -l≤u : (- l) ℚ≤ u
        -l≤u = trans-ℚ≤ { - l} (trans-ℚ≤ { - l}-l≤0 0≤l) l≤u
