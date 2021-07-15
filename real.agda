{-# OPTIONS --cubical --safe --exact-split #-}

module real where

open import base
open import cubical
open import equality
open import functions
open import hlevel
open import isomorphism
open import rational
open import rational.difference
open import rational.order
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import truncation
open import univalence

private
  variable
    ℓ : Level


isLowerSet : Pred Rational ℓ -> Type ℓ
isLowerSet L = (x y : Rational) -> x < y -> L y -> L x

isUpperSet : Pred Rational ℓ -> Type ℓ
isUpperSet U = (x y : Rational) -> x < y -> U x -> U y

isLowerOpen : Pred Rational ℓ -> Type ℓ
isLowerOpen U = (x : Rational) -> U x -> ∃[ y ∈ Rational ] (y < x × U y)

isUpperOpen : Pred Rational ℓ -> Type ℓ
isUpperOpen L = (x : Rational) -> L x -> ∃[ y ∈ Rational ] (x < y × L y)

record Real (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    L : Pred Rational ℓ
    U : Pred Rational ℓ
    isProp-L : isPropValuedPred L
    isProp-U : isPropValuedPred U
    Inhabited-L : Inhabited L
    Inhabited-U : Inhabited U
    isLowerSet-L : isLowerSet L
    isUpperSet-U : isUpperSet U
    isUpperOpen-L : isUpperOpen L
    isLowerOpen-U : isLowerOpen U
    disjoint : Universal (Comp (L ∩ U))
    located : (x y : Rational) -> x < y -> ∥ L x ⊎ U y ∥

ℝ = Real ℓ-zero

ℚ->ℝ : ℚ -> ℝ
ℚ->ℝ q1 = record
  { L = L
  ; U = U
  ; isProp-L = \q2 -> isProp-< {q2} {q1}
  ; isProp-U = \q2 -> isProp-< {q1} {q2}
  ; Inhabited-L = Inhabited-L
  ; Inhabited-U = Inhabited-U
  ; isLowerSet-L = \q2 q3 q2<q3 q3<q1 -> trans-< {q2} {q3} {q1} q2<q3 q3<q1
  ; isUpperSet-U = \q2 q3 q2<q3 q1<q2 -> trans-< {q1} {q2} {q3} q1<q2 q2<q3
  ; isUpperOpen-L = isUpperOpen-L
  ; isLowerOpen-U = isLowerOpen-U
  ; disjoint = \q2 (l , u) -> asym-< {q2} {q1} l u
  ; located = located
  }
  where
  L = \q2 -> q2 < q1
  U = \q2 -> q1 < q2
  Inhabited-L : Inhabited L
  Inhabited-L = ∣ q1 r+ (r- 1r)  , lt2 ∣
    where
    lt1 : (q1 r+ (r- 1r)) < (q1 r+ 0r)
    lt1 = r+₁-preserves-order q1 (r- 1r) 0r (r--flips-order 0r 1r (Pos-0< 1r Pos-1r))
    lt2 : (q1 r+ (r- 1r)) < q1
    lt2 = subst ((q1 r+ (r- 1r)) <_) (r+-right-zero q1) lt1

  Inhabited-U : Inhabited U
  Inhabited-U = ∣ q1 r+ 1r  , lt2 ∣
    where
    lt1 : (q1 r+ 1r) > (q1 r+ 0r)
    lt1 = r+₁-preserves-order q1 0r 1r (Pos-0< 1r Pos-1r)
    lt2 : (q1 r+ 1r) > q1
    lt2 = subst ((q1 r+ 1r) >_) (r+-right-zero q1) lt1

  located : (q2 q3 : Rational) -> q2 < q3 -> ∥ q2 < q1 ⊎ q1 < q3 ∥
  located q2 q3 lt = ∥-map handle (dense-< {q2} {q3} lt)
    where
    handle : Σ[ z ∈ ℚ ] (q2 < z × z < q3) -> q2 < q1 ⊎ q1 < q3
    handle (z , q2<z , z<q3) = handle2 (decide-< q1 z) (decide-< z q1)
      where
      handle2 : Dec (q1 < z) -> Dec (z < q1) -> q2 < q1 ⊎ q1 < q3
      handle2 (yes lt) _        = inj-r (trans-< {q1} {z} {q3} lt z<q3)
      handle2 (no _)   (yes lt) = inj-l (trans-< {q2} {z} {q1} q2<z lt)
      handle2 (no q1≮z) (no z≮q1) = inj-l (subst (q2 <_) (connected-< {z} {q1} z≮q1 q1≮z) q2<z)

  isUpperOpen-L : (q2 : ℚ) -> L q2 -> ∃[ q3 ∈ ℚ ] (q2 < q3 × L q3)
  isUpperOpen-L q2 q2<q1 = dense-< {q2} {q1} q2<q1

  isLowerOpen-U : (q2 : ℚ) -> U q2 -> ∃[ q3 ∈ ℚ ] (q3 < q2 × U q3)
  isLowerOpen-U q2 q1<q2 =
    ∥-map (\ (q3 , q1<q3 , q3<q2) -> q3 , q3<q2 , q1<q3) (dense-< {q1} {q2} q1<q2)

0ℝ : ℝ
0ℝ = ℚ->ℝ 0r

1ℝ : ℝ
1ℝ = ℚ->ℝ 1r

module _ (x : ℝ) where
  private
    module x = Real x

  ℝ->Pos-U : ∃[ q ∈ ℚ⁺ ] (x.U ⟨ q ⟩)
  ℝ->Pos-U = ∥-map handle x.Inhabited-U
    where
    handle : Σ[ q ∈ ℚ ] (x.U q) -> Σ[ q ∈ ℚ⁺ ] (x.U ⟨ q ⟩)
    handle (q , uq) = handle2 (split-< 0r q)
      where
      handle2 : (0r < q) ⊎ (q ℚ≤ 0r) -> Σ[ q ∈ ℚ⁺ ] (x.U ⟨ q ⟩)
      handle2 (inj-l 0<q) = (q , subst Posℚ (r+-right-zero q) 0<q) , uq
      handle2 (inj-r q≤0) = (1r , Pos-1r) , x.isUpperSet-U q 1r q<1r uq
        where
        q<1r : q < 1r
        q<1r = (trans-≤-< {q} {0r} {1r} q≤0 (Pos-0< 1r Pos-1r))

  ℝ->Neg-L : ∃[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩)
  ℝ->Neg-L = ∥-map handle x.Inhabited-L
    where
    handle : Σ[ q ∈ ℚ ] (x.L q) -> Σ[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩)
    handle (q , lq) = handle2 (split-< q 0r)
      where
      handle2 : (q < 0r) ⊎ (0r ℚ≤ q) -> Σ[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩)
      handle2 (inj-l q<0) = (q , Neg-q) , lq
        where
        Neg-d : Negℚ (diffℚ 0r q)
        Neg-d = subst Negℚ (sym (diffℚ-anticommute 0r q)) (r--flips-sign _ _ q<0)

        Neg-q : Negℚ q
        Neg-q = subst Negℚ (r+-right-zero q) Neg-d
      handle2 (inj-r 0≤q) = ((r- 1r) , (r--flips-sign _ _ Pos-1r)) ,
                            x.isLowerSet-L (r- 1r) q -1r<q lq
        where
        -1r<q : (r- 1r) < q
        -1r<q = trans-<-≤ {r- 1r} {0r} {q}
                  (subst Posℚ (RationalRing.minus-double-inverse >=>
                               (sym (r+-left-zero (r- (r- 1r)))))
                              Pos-1r)
                  0≤q

  isLowerSet≤ : (q r : ℚ) -> (q ℚ≤ r) -> x.L r -> x.L q
  isLowerSet≤ q r q≤r lr = unsquash (x.isProp-L q) (∥-map handle (x.isUpperOpen-L r lr))
    where
    handle : Σ[ s ∈ ℚ ] (r < s × x.L s) -> x.L q
    handle (s , r<s , ls) = x.isLowerSet-L q s (trans-≤-< {q} {r} {s} q≤r r<s) ls

  isUpperSet≤ : (q r : ℚ) -> (q ℚ≤ r) -> x.U q -> x.U r
  isUpperSet≤ q r q≤r uq = unsquash (x.isProp-U r) (∥-map handle (x.isLowerOpen-U q uq))
    where
    handle : Σ[ s ∈ ℚ ] (s < q × x.U s) -> x.U r
    handle (s , s<q , us) = x.isUpperSet-U s r (trans-<-≤ {s} {q} {r} s<q q≤r) us


  LowerOpen-Pos : (q : ℚ⁺) -> (x.U ⟨ q ⟩) -> ∃[ r ∈ ℚ⁺ ] (⟨ r ⟩ < ⟨ q ⟩ × x.U ⟨ r ⟩)
  LowerOpen-Pos (q , pos-q) xu-q = ∥-map handle (x.isLowerOpen-U q xu-q)
    where
    handle : Σ[ r ∈ ℚ ] (r < q × x.U r) -> Σ[ r ∈ ℚ⁺ ] (⟨ r ⟩ < q × x.U ⟨ r ⟩)
    handle (r , r<q , xu-r) = handle2 (split-< q/2 r)
      where
      q/2 : ℚ
      q/2 = 1/2r r* q

      q/2<q : q/2 < q
      q/2<q = subst (q/2 <_) (r*-left-one q) (r*₂-preserves-order 1/2r 1r (q , pos-q) 1/2r<1r)

      pos-q/2 : Posℚ q/2
      pos-q/2 = r*₁-preserves-sign (1/2r , Pos-1/ℕ _) q pos-q

      handle2 : (q/2 < r) ⊎ (r ℚ≤ q/2) ->  Σ[ r ∈ ℚ⁺ ] (⟨ r ⟩ < q × x.U ⟨ r ⟩)
      handle2 (inj-l q/2<r) = (r , Pos-< q/2 r (inj-l pos-q/2) q/2<r) , r<q , xu-r
      handle2 (inj-r r≤q/2) = (q/2 , pos-q/2) , q/2<q , isUpperSet≤ r q/2 r≤q/2 xu-r



_ℝ<'_ : ℝ -> ℝ -> Type₀
x ℝ<' y = Σ[ q ∈ ℚ ] (Real.U x q × Real.L y q)

_ℝ<_ : ℝ -> ℝ -> Type₀
x ℝ< y = ∃[ q ∈ ℚ ] (Real.U x q × Real.L y q)


ℚ->ℝ-preserves-< : (q1 q2 : ℚ) -> (q1 < q2) -> (ℚ->ℝ q1) ℝ< (ℚ->ℝ q2)
ℚ->ℝ-preserves-< q1 q2 lt = dense-< {q1} {q2} lt

isProp-ℝ< : (x y : ℝ) -> isProp (x ℝ< y)
isProp-ℝ< x y = squash

irrefl-ℝ< : Irreflexive _ℝ<_
irrefl-ℝ< {x} x<x = unsquash isPropBot (∥-map handle x<x)
  where
  handle : x ℝ<' x -> Bot
  handle (q , (u , l)) = Real.disjoint x q (l , u)

ℝ-bounds->ℚ< : (x : ℝ) (q1 q2 : ℚ) -> (Real.L x q1) -> (Real.U x q2) -> q1 < q2
ℝ-bounds->ℚ< x q1 q2 l u = handle (trichotomous-< q1 q2)
  where
  handle : Tri (q1 < q2) (q1 == q2) (q2 < q1) -> q1 < q2
  handle (tri< lt _ _ ) = lt
  handle (tri= _  p _ ) = bot-elim (Real.disjoint x q1 (l , (subst (Real.U x) (sym p) u)))
  handle (tri> _  _ lt) = bot-elim (Real.disjoint x q1 (l , (Real.isUpperSet-U x q2 q1 lt u)))

ℝ-bounds->¬ℚ≤ : (x : ℝ) (q1 q2 : ℚ) -> (Real.L x q1) -> (Real.U x q2) -> ¬ (q2 ℚ≤ q1)
ℝ-bounds->¬ℚ≤ x q1 q2 lq1 uq2 q2≤q1 =
  irrefl-< {q2} (trans-≤-< {q2} {q1} {q2} q2≤q1 (ℝ-bounds->ℚ< x q1 q2 lq1 uq2))

trans-ℝ< : Transitive _ℝ<_
trans-ℝ< {x} {y} {z} x<y y<z = (∥-map2 handle x<y y<z)
  where
  handle : x ℝ<' y -> y ℝ<' z -> x ℝ<' z
  handle (q1 , (ux-q1 , ly-q1)) (q2 , (uy-q2 , lz-q2)) = (q1 , (ux-q1 , lz-q1))
    where
    q1<q2 = ℝ-bounds->ℚ< y q1 q2 ly-q1 uy-q2
    lz-q1 : Real.L z q1
    lz-q1 = Real.isLowerSet-L z q1 q2 q1<q2 lz-q2

asym-ℝ< : Asymmetric _ℝ<_
asym-ℝ< {x} {y} x<y y<x = irrefl-ℝ< {x} (trans-ℝ< {x} {y} {x} x<y y<x)

abstract
  LU-paths->path : (x y : ℝ)
                   -> (∀ q -> (Real.L x q) == (Real.L y q))
                   -> (∀ q -> (Real.U x q) == (Real.U y q))
                   -> x == y
  LU-paths->path x y lp up = (\i -> record
    { L = lp' i
    ; U = up' i
    ; isProp-L = isProp-L i
    ; isProp-U = isProp-U i
    ; Inhabited-L =
      isProp->PathP (\i -> squash {A = Σ ℚ (lp' i)}) (Real.Inhabited-L x) (Real.Inhabited-L y) i
    ; Inhabited-U =
      isProp->PathP (\i -> squash {A = Σ ℚ (up' i)}) (Real.Inhabited-U x) (Real.Inhabited-U y) i
    ; isLowerSet-L =
      isProp->PathP isProp-isLowerSet (Real.isLowerSet-L x) (Real.isLowerSet-L y) i
    ; isUpperSet-U =
      isProp->PathP isProp-isUpperSet (Real.isUpperSet-U x) (Real.isUpperSet-U y) i
    ; isUpperOpen-L =
      isProp->PathP isProp-isUpperOpen (Real.isUpperOpen-L x) (Real.isUpperOpen-L y) i
    ; isLowerOpen-U =
      isProp->PathP isProp-isLowerOpen (Real.isLowerOpen-U x) (Real.isLowerOpen-U y) i
    ; disjoint =
      isProp->PathP {B = \i -> (q : Rational) -> (lp q i) × (up q i) -> Bot}
        (\i -> isPropΠ2 (\ _ _ -> isPropBot)) (Real.disjoint x) (Real.disjoint y) i
    ; located =
      isProp->PathP {B = \i -> (q r : Rational) -> (q < r) -> ∥ lp q i ⊎ up r i ∥}
        (\i -> isPropΠ3 (\ _ _ _ -> squash)) (Real.located x) (Real.located y) i
    })
    where
    lp' : (Real.L x) == (Real.L y)
    lp' i q = lp q i
    up' : (Real.U x) == (Real.U y)
    up' i q = up q i
    isProp-L : (i : I) (q : ℚ) -> isProp (lp' i q)
    isProp-L i q = isProp->PathP (\i -> isProp-isProp {A = lp' i q})
                                 (Real.isProp-L x q) (Real.isProp-L y q) i
    isProp-U : (i : I) (q : ℚ) -> isProp (up' i q)
    isProp-U i q = isProp->PathP (\i -> isProp-isProp {A = up' i q})
                                 (Real.isProp-U x q) (Real.isProp-U y q) i

    isProp-isLowerSet : (i : I) -> isProp (isLowerSet (lp' i))
    isProp-isLowerSet i = isPropΠ4 (\q _ _ _ -> isProp-L i q)
    isProp-isUpperSet : (i : I) -> isProp (isUpperSet (up' i))
    isProp-isUpperSet i = isPropΠ4 (\_ q _ _ -> isProp-U i q)

    isProp-isLowerOpen : (i : I) -> isProp (isLowerOpen (up' i))
    isProp-isLowerOpen i = isPropΠ2 (\_ _ -> squash)
    isProp-isUpperOpen : (i : I) -> isProp (isUpperOpen (lp' i))
    isProp-isUpperOpen i = isPropΠ2 (\_ _ -> squash)

private
  record RawCut (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      hL : ℚ -> hProp ℓ
      hU : ℚ -> hProp ℓ

    L : Pred ℚ ℓ
    L q = fst (hL q)
    U : Pred ℚ ℓ
    U q = fst (hU q)

    isProp-L : isPropValuedPred L
    isProp-L q = snd (hL q)
    isProp-U : isPropValuedPred U
    isProp-U q = snd (hU q)

  isSet-RawCut : isSet (RawCut ℓ)
  isSet-RawCut x y p1 p2 i j = record
    { hL = \q -> isSet-hProp (RawCut.hL x q) (RawCut.hL y q)
                             (cong (\z -> RawCut.hL z q) p1)
                             (cong (\z -> RawCut.hL z q) p2) i j
    ; hU = \q -> isSet-hProp (RawCut.hU x q) (RawCut.hU y q)
                             (cong (\z -> RawCut.hU z q) p1)
                             (cong (\z -> RawCut.hU z q) p2) i j
    }

  record isGoodCut {ℓ : Level} (c : RawCut ℓ) : Type (ℓ-suc ℓ) where
    private
      module c = RawCut c
    field
      Inhabited-L : Inhabited c.L
      Inhabited-U : Inhabited c.U
      isLowerSet-L : isLowerSet c.L
      isUpperSet-U : isUpperSet c.U
      isUpperOpen-L : isUpperOpen c.L
      isLowerOpen-U : isLowerOpen c.U
      disjoint : Universal (Comp (c.L ∩ c.U))
      located : (x y : ℚ) -> x < y -> ∥ c.L x ⊎ c.U y ∥

  isProp-isGoodCut : {ℓ : Level} {c : RawCut ℓ} -> isProp (isGoodCut c)
  isProp-isGoodCut {c = c} g1 g2 = (\i -> record
    { Inhabited-L = squash g1.Inhabited-L g2.Inhabited-L i
    ; Inhabited-U = squash g1.Inhabited-U g2.Inhabited-U i
    ; isLowerSet-L = isPropΠ4 (\x _ _ _ -> c.isProp-L x) g1.isLowerSet-L g2.isLowerSet-L i
    ; isUpperSet-U = isPropΠ4 (\_ y _ _ -> c.isProp-U y) g1.isUpperSet-U g2.isUpperSet-U i
    ; isUpperOpen-L = isPropΠ2 (\_ _ -> squash) g1.isUpperOpen-L g2.isUpperOpen-L i
    ; isLowerOpen-U = isPropΠ2 (\_ _ -> squash) g1.isLowerOpen-U g2.isLowerOpen-U i
    ; disjoint = isPropΠ2 (\_ _ -> isPropBot) g1.disjoint g2.disjoint i
    ; located = isPropΠ3 (\_ _ _ -> squash) g1.located g2.located i
    })
    where
    module g1 = isGoodCut g1
    module g2 = isGoodCut g2
    module c = RawCut c

  GoodCut : (ℓ : Level) -> Type (ℓ-suc ℓ)
  GoodCut ℓ = Σ (RawCut ℓ) isGoodCut

  isSet-GoodCut : isSet (GoodCut ℓ)
  isSet-GoodCut = isSetΣ isSet-RawCut (\_ -> isProp->isSet isProp-isGoodCut)

  GoodCut₀ = GoodCut ℓ-zero

  GoodCut==ℝ : GoodCut₀ == ℝ
  GoodCut==ℝ = ua (isoToEquiv i)
    where
    open Iso
    i : Iso GoodCut₀ ℝ
    i .fun (c , g) = record
      { L = c.L
      ; U = c.U
      ; isProp-L = c.isProp-L
      ; isProp-U = c.isProp-U
      ; Inhabited-L = g.Inhabited-L
      ; Inhabited-U = g.Inhabited-U
      ; isLowerSet-L = g.isLowerSet-L
      ; isUpperSet-U = g.isUpperSet-U
      ; isUpperOpen-L = g.isUpperOpen-L
      ; isLowerOpen-U = g.isLowerOpen-U
      ; disjoint = g.disjoint
      ; located = g.located
      }
      where
      module c = RawCut c
      module g = isGoodCut g
    i .inv r = record
      { hL = \q -> r.L q , r.isProp-L q
      ; hU = \q -> r.U q , r.isProp-U q
      } , record
      { Inhabited-L = r.Inhabited-L
      ; Inhabited-U = r.Inhabited-U
      ; isLowerSet-L = r.isLowerSet-L
      ; isUpperSet-U = r.isUpperSet-U
      ; isUpperOpen-L = r.isUpperOpen-L
      ; isLowerOpen-U = r.isLowerOpen-U
      ; disjoint = r.disjoint
      ; located = r.located
      }
      where
      module r = Real r
    i .rightInv _ = refl
    i .leftInv _ = refl

isSet-ℝ : isSet ℝ
isSet-ℝ = subst isSet GoodCut==ℝ isSet-GoodCut

connected-ℝ< : (x y : ℝ) -> ¬ (x ℝ< y) -> ¬ (y ℝ< x) -> x == y
connected-ℝ< x y x≮y y≮x = LU-paths->path x y l-path u-path
  where
  l-fun : (x y : ℝ) (q : ℚ) -> ¬ (y ℝ< x) -> Real.L x q -> Real.L y q
  l-fun x y q y≮x lx-q = unsquash (Real.isProp-L y q) (∥-map handle (Real.isUpperOpen-L x q lx-q))
    where
    handle : Σ[ r ∈ ℚ ] (q < r × (Real.L x r)) -> Real.L y q
    handle (r , (q<r , lx-r)) = unsquash (Real.isProp-L y q) (∥-map handle2 (Real.located y q r q<r))
      where
      handle2 : (Real.L y q ⊎ Real.U y r) -> Real.L y q
      handle2 (inj-l ly-q) = ly-q
      handle2 (inj-r uy-r) = bot-elim (y≮x ∣ (r , (uy-r , lx-r)) ∣)

  l-path : (q : ℚ) -> Real.L x q == Real.L y q
  l-path q = ua (isoToEquiv i)
    where
    open Iso
    i : Iso (Real.L x q) (Real.L y q)
    i .fun = l-fun x y q y≮x
    i .inv = l-fun y x q x≮y
    i .rightInv _ = Real.isProp-L y q _ _
    i .leftInv _ = Real.isProp-L x q _ _

  u-fun : (x y : ℝ) (q : ℚ) -> ¬ (x ℝ< y) -> Real.U x q -> Real.U y q
  u-fun x y q x≮y ux-q = unsquash (Real.isProp-U y q) (∥-map handle (Real.isLowerOpen-U x q ux-q))
    where
    handle : Σ[ r ∈ ℚ ] (q > r × (Real.U x r)) -> Real.U y q
    handle (r , (r<q , ux-r)) = unsquash (Real.isProp-U y q) (∥-map handle2 (Real.located y r q r<q))
      where
      handle2 : (Real.L y r ⊎ Real.U y q) -> Real.U y q
      handle2 (inj-l ly-r) = bot-elim (x≮y ∣ (r , (ux-r , ly-r)) ∣)
      handle2 (inj-r uy-q) = uy-q

  u-path : (q : ℚ) -> Real.U x q == Real.U y q
  u-path q = ua (isoToEquiv i)
    where
    open Iso
    i : Iso (Real.U x q) (Real.U y q)
    i .fun = u-fun x y q x≮y
    i .inv = u-fun y x q y≮x
    i .rightInv _ = Real.isProp-U y q _ _
    i .leftInv _ = Real.isProp-U x q _ _

comparison-ℝ< : (x y z : ℝ) -> x ℝ< z -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
comparison-ℝ< x y z x<z = ∥-bind handle x<z
  where
  handle : Σ[ q ∈ ℚ ] (Real.U x q × Real.L z q) -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
  handle (q , (ux-q , lz-q)) = ∥-bind handle2 (Real.isLowerOpen-U x q ux-q)
    where
    handle2 : Σ[ r ∈ ℚ ] (r < q × Real.U x r) -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
    handle2 (r , (r<q , ux-r)) = ∥-bind handle3 (Real.located y r q r<q)
      where
      handle3 : (Real.L y r ⊎ Real.U y q) -> ∥ (x ℝ< y) ⊎ (y ℝ< z) ∥
      handle3 (inj-l ly-r) = ∣ inj-l (∣ r , (ux-r , ly-r) ∣) ∣
      handle3 (inj-r uy-q) = ∣ inj-r (∣ q , (uy-q , lz-q) ∣) ∣

ℝ<->U : (x : ℝ) (q : ℚ) -> x ℝ< (ℚ->ℝ q) -> Real.U x q
ℝ<->U x q x<q = unsquash (x.isProp-U q) (∥-map handle x<q)
  where
  module x = Real x
  handle : x ℝ<' (ℚ->ℝ q) -> Real.U x q
  handle (r , xu-r , r<q) = x.isUpperSet-U r q r<q xu-r


ℝ<->L : (q : ℚ) (x : ℝ) -> (ℚ->ℝ q) ℝ< x -> Real.L x q
ℝ<->L q x q<x = unsquash (x.isProp-L q) (∥-map handle q<x)
  where
  module x = Real x
  handle : (ℚ->ℝ q) ℝ<' x -> Real.L x q
  handle (r , q<r , xl-r) = x.isLowerSet-L q r q<r xl-r


_ℝ#_ : ℝ -> ℝ -> Type₀
x ℝ# y = (x ℝ< y) ⊎ (y ℝ< x)

isProp-ℝ# : (x y : ℝ) -> isProp (x ℝ# y)
isProp-ℝ# x y = isProp⊎ (isProp-ℝ< x y) (isProp-ℝ< y x) (asym-ℝ< {x} {y})

irrefl-ℝ# : Irreflexive _ℝ#_
irrefl-ℝ# {x} (inj-l x<x) = irrefl-ℝ< {x} x<x
irrefl-ℝ# {x} (inj-r x<x) = irrefl-ℝ< {x} x<x

sym-ℝ# : Symmetric _ℝ#_
sym-ℝ# {x} (inj-l x<y) = (inj-r x<y)
sym-ℝ# {x} (inj-r y<x) = (inj-l y<x)

comparison-ℝ# : (x y z : ℝ) -> (x ℝ# z) -> ∥ (x ℝ# y) ⊎ (y ℝ# z) ∥
comparison-ℝ# x y z (inj-l x<z) = ∥-map handle (comparison-ℝ< x y z x<z)
  where
  handle : (x ℝ< y) ⊎ (y ℝ< z) → (x ℝ# y) ⊎ (y ℝ# z)
  handle (inj-l lt) = (inj-l (inj-l lt))
  handle (inj-r lt) = (inj-r (inj-l lt))
comparison-ℝ# x y z (inj-r z<x) = ∥-map handle (comparison-ℝ< z y x z<x)
  where
  handle : (z ℝ< y) ⊎ (y ℝ< x) → (x ℝ# y) ⊎ (y ℝ# z)
  handle (inj-l lt) = (inj-r (inj-r lt))
  handle (inj-r lt) = (inj-l (inj-r lt))

tight-ℝ# : (x y : ℝ) -> ¬(x ℝ# y) -> x == y
tight-ℝ# x y p = connected-ℝ< x y (p ∘ inj-l) (p ∘ inj-r)

ℝInv : Pred ℝ ℓ-zero
ℝInv x = x ℝ# 0ℝ

isProp-ℝInv : (x : ℝ) -> isProp (ℝInv x)
isProp-ℝInv x = isProp-ℝ# x 0ℝ
