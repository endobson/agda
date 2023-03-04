{-# OPTIONS --cubical --safe --exact-split #-}

module real.interval where

open import additive-group
open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-ring
open import ordered-semiring
open import rational
open import rational.minmax
open import rational.order
open import rational.proper-interval
open import real
open import real.order
open import real.rational
open import real.sequence
open import truncation
open import univalence

ℝ∈Iℚ : ℝ -> Iℚ -> Type₀
ℝ∈Iℚ z a = Real.L z (Iℚ.l a) × Real.U z (Iℚ.u a)

ℝ∈Iℚ->Overlap : (z : ℝ) (a b : Iℚ) -> ℝ∈Iℚ z a -> ℝ∈Iℚ z b -> Overlap a b
ℝ∈Iℚ->Overlap z a b (al , au) (bl , bu) =
  weaken-< (ℝ-bounds->ℚ< z bl au) , weaken-< (ℝ-bounds->ℚ< z al bu)

ℝ∈Iℚ-intersect : (z : ℝ) (a b : Iℚ) -> (ea : ℝ∈Iℚ z a) -> (eb : ℝ∈Iℚ z b) ->
                 ℝ∈Iℚ z (i-intersect a b (ℝ∈Iℚ->Overlap z a b ea eb))
ℝ∈Iℚ-intersect z a b (al , au) (bl , bu) =
  maxℚ-property {P = Real.L z} _ _ al bl ,
  minℚ-property {P = Real.U z} _ _ au bu

ℝ∈Iℚ->¬Constant : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z a -> ¬ (ConstantI a)
ℝ∈Iℚ->¬Constant z a (al , au) p =
  Real.disjoint z (Iℚ.u a) (subst (Real.L z) p al , au)

ℝ∈Iℚ->NonConstant : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z a -> NonConstantI a
ℝ∈Iℚ->NonConstant z a (al , au) = (ℝ-bounds->ℚ< z al au)

ℝ-bounds->Iℚ : (x : ℝ) -> {l u : ℚ} -> Real.L x l -> Real.U x u -> Iℚ
ℝ-bounds->Iℚ x l<x x<u =
  (Iℚ-cons _ _ (weaken-< (ℝ-bounds->ℚ< x l<x x<u)))

isProp-ℝ∈Iℚ : (z : ℝ) (a : Iℚ) -> isProp (ℝ∈Iℚ z a)
isProp-ℝ∈Iℚ z (Iℚ-cons l u _) = isProp× (Real.isProp-L z l) (Real.isProp-U z u)

ℝ∈Iℚ->path : (x y : ℝ) -> (f : (q : Iℚ) -> ℝ∈Iℚ x q -> ℝ∈Iℚ y q) -> x == y
ℝ∈Iℚ->path x y f = LU-paths->path x y L-path U-path
  where
  module x = Real x
  module y = Real y

  f-L : (q : ℚ) -> x.L q -> y.L q
  f-L q xl-q = unsquash (y.isProp-L q) (∥-map handle x.Inhabited-U)
    where
    handle : Σ ℚ x.U -> y.L q
    handle (r , xu-r) = fst (f xi (xl-q , xu-r))
      where
      xi = ℝ-bounds->Iℚ x xl-q xu-r

  f-U : (q : ℚ) -> x.U q -> y.U q
  f-U q xu-q = unsquash (y.isProp-U q) (∥-map handle x.Inhabited-L)
    where
    handle : Σ ℚ x.L -> y.U q
    handle (r , xl-r) = snd (f xi (xl-r , xu-q))
      where
      xi = ℝ-bounds->Iℚ x xl-r xu-q

  L-path : (q : ℚ) -> x.L q == y.L q
  L-path q = ua (isoToEquiv i)
    where
    open Iso
    i : Iso (x.L q) (y.L q)
    i .rightInv _ = y.isProp-L q _ _
    i .leftInv _ = x.isProp-L q _ _
    i .fun = f-L q
    i .inv yl-q = unsquash (x.isProp-L q) (∥-bind handle (y.isUpperOpen-L q yl-q))
      where
      handle : Σ[ q' ∈ ℚ ] (q < q' × y.L q') -> ∥ x.L q ∥
      handle (q' , q<q' , yl-q')  = ∥-bind handle2 (x.located q q' q<q')
        where
        handle2 : (x.L q ⊎ x.U q') -> ∥ x.L q ∥
        handle2 (inj-l xl-q) = ∣ xl-q ∣
        handle2 (inj-r xu-q') = bot-elim (y.disjoint q' (yl-q' , f-U q' xu-q'))

  U-path : (q : ℚ) -> x.U q == y.U q
  U-path q = ua (isoToEquiv i)
    where
    open Iso
    i : Iso (x.U q) (y.U q)
    i .rightInv _ = y.isProp-U q _ _
    i .leftInv _ = x.isProp-U q _ _
    i .fun = f-U q
    i .inv yu-q = unsquash (x.isProp-U q) (∥-bind handle (y.isLowerOpen-U q yu-q))
      where
      handle : Σ[ q' ∈ ℚ ] (q' < q × y.U q') -> ∥ x.U q ∥
      handle (q' , q'<q , yu-q')  = ∥-bind handle2 (x.located q' q q'<q)
        where
        handle2 : (x.L q' ⊎ x.U q) -> ∥ x.U q ∥
        handle2 (inj-l xl-q') = bot-elim (y.disjoint q' (f-L q' xl-q' , yu-q'))
        handle2 (inj-r xu-q) = ∣ xu-q ∣

ℝ∈Iℚ-⊆ : (x : ℝ) {a b : Iℚ} -> a i⊆ b -> ℝ∈Iℚ x a -> ℝ∈Iℚ x b
ℝ∈Iℚ-⊆ x {a} {b} (i⊆-cons bl≤al au≤bu) (xl-a , xu-a) =
  isLowerSet≤ x bl≤al xl-a , isUpperSet≤ x au≤bu xu-a

ℝ∈Iℚ-Pos : (x : ℝ) -> 0ℝ ℝ< x -> ∃[ b ∈ Iℚ ] (ℝ∈Iℚ x b × PosI b)
ℝ∈Iℚ-Pos x 0<x = ∥-map2 handle (x.isUpperOpen-L 0r (ℝ<->L 0r x 0<x)) x.Inhabited-U
  where
  module x = Real x
  handle : Σ[ q ∈ ℚ ] (0r < q × x.L q) -> Σ ℚ x.U -> Σ[ b ∈ Iℚ ] (ℝ∈Iℚ x b × PosI b)
  handle (q , 0<q , xl-q) (r , xu-q) =
    ℝ-bounds->Iℚ x xl-q xu-q , (xl-q , xu-q) , 0<q


ℝ∈Iℚ-Pos-⊆ : (x : ℝ) (a : Iℚ) -> ℝ∈Iℚ x a -> 0ℝ ℝ< x -> ∃[ b ∈ Iℚ ] (b i⊆ a × ℝ∈Iℚ x b × PosI b)
ℝ∈Iℚ-Pos-⊆ x a x∈a 0<x = ∥-map handle (ℝ∈Iℚ-Pos x 0<x)
  where
  module x = Real x
  handle : Σ[ b ∈ Iℚ ] (ℝ∈Iℚ x b × PosI b) -> Σ[ c ∈ Iℚ ] (c i⊆ a × ℝ∈Iℚ x c × PosI c)
  handle (b , x∈b , pos-b) = c , c⊆a , x∈c , pos-c
    where
    o-ab = ℝ∈Iℚ->Overlap x a b x∈a x∈b
    c = i-intersect a b o-ab
    x∈c = ℝ∈Iℚ-intersect x a b x∈a x∈b

    c⊆a = i-intersect-⊆₁ a b o-ab
    c⊆b = i-intersect-⊆₂ a b o-ab
    pos-c = i⊆-preserves-PosI c⊆b pos-b

tighter-ℝ∈Iℚ : (x : ℝ) -> (qi : Iℚ) -> (ℝ∈Iℚ x qi) -> ∃[ qi2 ∈ Iℚ ] ((qi2 i⊂ qi) × ℝ∈Iℚ x qi2)
tighter-ℝ∈Iℚ x (Iℚ-cons l u _) (l<x , x<u) =
  ∥-map2 (\{ (l' , l<l' , l'<x) (u' , u'<u , x<u') ->
             (ℝ-bounds->Iℚ x l'<x x<u') ,
             (i⊂-cons l<l' u'<u) ,
             (l'<x , x<u') })
         (Real.isUpperOpen-L x l l<x) (Real.isLowerOpen-U x u x<u)

find-small-ℝ∈Iℚ : (x : ℝ) (ε : ℚ⁺) -> ∃[ qi ∈ Iℚ ] (ℝ∈Iℚ x qi × i-width qi ≤ ⟨ ε ⟩)
find-small-ℝ∈Iℚ x ε = ∥-map handle (find-open-ball x ε)
  where
  handle : OpenBall x ⟨ ε ⟩ -> Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ x qi × i-width qi ≤ ⟨ ε ⟩)
  handle (l , u , l<x , x<u , diff=ε) =
    (ℝ-bounds->Iℚ x l<x x<u) ,
    (l<x , x<u) ,
    subst2 _≤_ refl diff=ε refl-≤

private
  tighter-ε : (x : ℝ) (qi1 qi2 : Iℚ) -> (qi1 i⊂ qi2) ->
              Σ[ ε ∈ ℚ⁺ ] ((qi3 : Iℚ) -> i-width qi3 ≤ ⟨ ε ⟩ -> Overlap qi3 qi1 -> qi3 i⊆ qi2)
  tighter-ε x qi1@(Iℚ-cons l1 u1 _) qi2@(Iℚ-cons l2 u2 _) (i⊂-cons l2<l1 u1<u2) = (ε , 0<ε) , f
    where
    dl = (diff l2 l1)
    du = (diff u1 u2)
    ε = min dl du
    0<dl : 0# < dl
    0<dl = trans-=-< (sym +-inverse) (+₂-preserves-< l2<l1)
    0<du : 0# < du
    0<du = trans-=-< (sym +-inverse) (+₂-preserves-< u1<u2)
    0<ε : 0# < ε
    0<ε = minℚ-property {P = 0# <_} dl du 0<dl 0<du

    f : (qi3 : Iℚ) -> i-width qi3 ≤ ε -> Overlap qi3 qi1 -> qi3 i⊆ qi2
    f qi3@(Iℚ-cons l3 u3 _) w≤ε (l1≤u3 , l3≤u1) = i⊆-cons l2≤l3 u3≤u2
      where
      w = diff l3 u3
      -w = diff u3 l3
      l2≤l3 : l2 ≤ l3
      l2≤l3 = subst2 _≤_ diff-step diff-step (+-preserves-≤ l1≤u3 -dl≤-w)
        where
        -dl≤-w : (diff l1 l2) ≤ -w
        -dl≤-w = subst2 _≤_ (sym diff-anticommute) (sym diff-anticommute)
                        (minus-flips-≤ (trans-≤ w≤ε min-≤-left))
      u3≤u2 : u3 ≤ u2
      u3≤u2 = subst2 _≤_ diff-step diff-step (+-preserves-≤ l3≤u1 w≤du)
        where
        w≤du : w ≤ du
        w≤du = trans-≤ w≤ε min-≤-right


overlapping-ℝ∈Iℚs->path :
  (x y : ℝ) ->
  ((qi1 qi2 : Iℚ) -> ℝ∈Iℚ x qi1 -> ℝ∈Iℚ y qi2 -> Overlap qi1 qi2) ->
  x == y
overlapping-ℝ∈Iℚs->path x y f = ℝ∈Iℚ->path x y g
  where
  g : (qi : Iℚ) -> ℝ∈Iℚ x qi -> ℝ∈Iℚ y qi
  g qi x∈qi = unsquash (isProp-ℝ∈Iℚ y qi) (∥-bind handle (tighter-ℝ∈Iℚ x qi x∈qi))
    where
    handle : Σ[ qi2 ∈ Iℚ ] ((qi2 i⊂ qi) × ℝ∈Iℚ x qi2) -> ∥ ℝ∈Iℚ y qi ∥
    handle (qi2 , qi2⊂qi , x∈qi2) = handle2 (tighter-ε x qi2 qi qi2⊂qi)
      where
      handle2 : Σ[ ε ∈ ℚ⁺ ] ((qi3 : Iℚ) -> i-width qi3 ≤ ⟨ ε ⟩ -> Overlap qi3 qi2 -> qi3 i⊆ qi) ->
                ∥ ℝ∈Iℚ y qi ∥
      handle2 (ε , h) = ∥-bind handle3 (find-small-ℝ∈Iℚ y ε)
        where
        handle3 : Σ[ qi3 ∈ Iℚ ] (ℝ∈Iℚ y qi3 × i-width qi3 ≤ ⟨ ε ⟩) -> ∥ ℝ∈Iℚ y qi ∥
        handle3 (qi3 , y∈qi3 , w-qi3≤ε) = ∣ ℝ∈Iℚ-⊆ y qi3⊆qi y∈qi3 ∣
          where
          o-qi3-qi2 = sym-Overlap qi2 qi3 (f qi2 qi3 x∈qi2 y∈qi3)
          qi3⊆qi = h qi3 w-qi3≤ε o-qi3-qi2
