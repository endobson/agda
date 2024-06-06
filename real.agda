{-# OPTIONS --cubical --safe --exact-split #-}

module real where

open import additive-group
open import base
open import cubical
open import equality-path
open import hlevel
open import isomorphism
open import order
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import relation hiding (U)
open import semiring
open import sign
open import truncation
open import univalence

private
  variable
    ℓ : Level


isLowerSet : Pred ℚ ℓ -> Type ℓ
isLowerSet L = {x y : ℚ} -> x < y -> L y -> L x

isUpperSet : Pred ℚ ℓ -> Type ℓ
isUpperSet U = {x y : ℚ} -> x < y -> U x -> U y

isLowerOpen : Pred ℚ ℓ -> Type ℓ
isLowerOpen U = (x : ℚ) -> U x -> ∃[ y ∈ ℚ ] (y < x × U y)

isUpperOpen : Pred ℚ ℓ -> Type ℓ
isUpperOpen L = (x : ℚ) -> L x -> ∃[ y ∈ ℚ ] (x < y × L y)

record Real (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality ; pattern
  field
    L : Pred ℚ ℓ
    U : Pred ℚ ℓ
    isProp-L : isPropValuedPred L
    isProp-U : isPropValuedPred U
    Inhabited-L : Inhabited L
    Inhabited-U : Inhabited U
    isLowerSet-L : isLowerSet L
    isUpperSet-U : isUpperSet U
    isUpperOpen-L : isUpperOpen L
    isLowerOpen-U : isLowerOpen U
    disjoint : Universal (Comp (L ∩ U))
    located : (x y : ℚ) -> x < y -> ∥ L x ⊎ U y ∥

ℝ = Real ℓ-zero

module _ (x : ℝ) where
  private
    module x = Real x

  ℝ->Pos-U : ∃[ q ∈ ℚ⁺ ] (x.U ⟨ q ⟩)
  ℝ->Pos-U = ∥-map handle x.Inhabited-U
    where
    handle : Σ[ q ∈ ℚ ] (x.U q) -> Σ[ q ∈ ℚ⁺ ] (x.U ⟨ q ⟩)
    handle (q , uq) = handle2 (split-< 0# q)
      where
      handle2 : (0# < q) ⊎ (q ≤ 0#) -> Σ[ q ∈ ℚ⁺ ] (x.U ⟨ q ⟩)
      handle2 (inj-l 0<q) = (q , 0<q) , uq
      handle2 (inj-r q≤0) = (1# , 0<1) , x.isUpperSet-U q<1 uq
        where
        q<1 : q < 1#
        q<1 = (trans-≤-< q≤0 0<1)

  ℝ->Neg-L : ∃[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩)
  ℝ->Neg-L = ∥-map handle x.Inhabited-L
    where
    handle : Σ[ q ∈ ℚ ] (x.L q) -> Σ[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩)
    handle (q , lq) = handle2 (split-< q 0#)
      where
      handle2 : (q < 0#) ⊎ (0# ≤ q) -> Σ[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩)
      handle2 (inj-l q<0) = (q , q<0) , lq
      handle2 (inj-r 0≤q) = ((- 1#) , -1<0) , x.isLowerSet-L -1<q lq
        where
        -1<0 = (minus-flips-0< 0<1)
        -1<q : (- 1#) < q
        -1<q = trans-<-≤ -1<0 0≤q

  isLowerSet≤ : {q r : ℚ} -> (q ≤ r) -> x.L r -> x.L q
  isLowerSet≤ {q} {r} q≤r lr = unsquash (x.isProp-L q) (∥-map handle (x.isUpperOpen-L r lr))
    where
    handle : Σ[ s ∈ ℚ ] (r < s × x.L s) -> x.L q
    handle (s , r<s , ls) = x.isLowerSet-L (trans-≤-< q≤r r<s) ls

  isUpperSet≤ : {q r : ℚ} -> (q ≤ r) -> x.U q -> x.U r
  isUpperSet≤ {q} {r} q≤r uq = unsquash (x.isProp-U r) (∥-map handle (x.isLowerOpen-U q uq))
    where
    handle : Σ[ s ∈ ℚ ] (s < q × x.U s) -> x.U r
    handle (s , s<q , us) = x.isUpperSet-U (trans-<-≤ s<q q≤r) us


  LowerOpen-Pos : (q : ℚ⁺) -> (x.U ⟨ q ⟩) -> ∃[ r ∈ ℚ⁺ ] (⟨ r ⟩ < ⟨ q ⟩ × x.U ⟨ r ⟩)
  LowerOpen-Pos (q , 0<q) xu-q = ∥-map handle (x.isLowerOpen-U q xu-q)
    where
    handle : Σ[ r ∈ ℚ ] (r < q × x.U r) -> Σ[ r ∈ ℚ⁺ ] (⟨ r ⟩ < q × x.U ⟨ r ⟩)
    handle (r , r<q , xu-r) = handle2 (split-< q/2 r)
      where
      q/2 : ℚ
      q/2 = 1/2r r* q

      q/2<q : q/2 < q
      q/2<q = trans-<-= (*₂-preserves-< 1/2r<1r 0<q) *-left-one

      0<q/2 : 0# < q/2
      0<q/2 = *-preserves-0< (Pos-1/ℕ _) 0<q

      handle2 : (q/2 < r) ⊎ (r ≤ q/2) ->  Σ[ r ∈ ℚ⁺ ] (⟨ r ⟩ < q × x.U ⟨ r ⟩)
      handle2 (inj-l q/2<r) = (r , trans-< 0<q/2 q/2<r) , r<q , xu-r
      handle2 (inj-r r≤q/2) = (q/2 , 0<q/2) , q/2<q , isUpperSet≤ r≤q/2 xu-r


abstract
  LU-paths->path : (x y : ℝ)
                   -> (∀ q -> (Real.L x q) == (Real.L y q))
                   -> (∀ q -> (Real.U x q) == (Real.U y q))
                   -> x == y
  LU-paths->path x@(record {}) y@(record {}) lp up = (\i -> record
    { L = lp' i
    ; U = up' i
    ; isProp-L = isProp-L i
    ; isProp-U = isProp-U i
    ; Inhabited-L =
      isProp->PathPᵉ (\i -> squash {A = Σ ℚ (lp' i)}) (Real.Inhabited-L x) (Real.Inhabited-L y) i
    ; Inhabited-U =
      isProp->PathPᵉ (\i -> squash {A = Σ ℚ (up' i)}) (Real.Inhabited-U x) (Real.Inhabited-U y) i
    ; isLowerSet-L =
      isProp->PathPᵉ isProp-isLowerSet (Real.isLowerSet-L x) (Real.isLowerSet-L y) i
    ; isUpperSet-U =
      isProp->PathPᵉ isProp-isUpperSet (Real.isUpperSet-U x) (Real.isUpperSet-U y) i
    ; isUpperOpen-L =
      isProp->PathPᵉ isProp-isUpperOpen (Real.isUpperOpen-L x) (Real.isUpperOpen-L y) i
    ; isLowerOpen-U =
      isProp->PathPᵉ isProp-isLowerOpen (Real.isLowerOpen-U x) (Real.isLowerOpen-U y) i
    ; disjoint =
      isProp->PathPᵉ {B = \i -> (q : ℚ) -> (lp q i) × (up q i) -> Bot}
        (\i -> isPropΠ2 (\ _ _ -> isPropBot)) (Real.disjoint x) (Real.disjoint y) i
    ; located =
      isProp->PathPᵉ {B = \i -> (q r : ℚ) -> (q < r) -> ∥ lp q i ⊎ up r i ∥}
        (\i -> isPropΠ3 (\ _ _ _ -> squash)) (Real.located x) (Real.located y) i
    })
    where
    lp' : (Real.L x) == (Real.L y)
    lp' i q = lp q i
    up' : (Real.U x) == (Real.U y)
    up' i q = up q i
    isProp-L : (i : I) (q : ℚ) -> isProp (lp' i q)
    isProp-L i q = isProp->PathPᵉ (\i -> isProp-isProp {A = lp' i q})
                                  (Real.isProp-L x q) (Real.isProp-L y q) i
    isProp-U : (i : I) (q : ℚ) -> isProp (up' i q)
    isProp-U i q = isProp->PathPᵉ (\i -> isProp-isProp {A = up' i q})
                                  (Real.isProp-U x q) (Real.isProp-U y q) i

    isProp-isLowerSet : (i : I) -> isProp (isLowerSet (lp' i))
    isProp-isLowerSet i = isPropΠⁱ2 (\q _ -> isPropΠ2 (\_ _ -> isProp-L i q))
    isProp-isUpperSet : (i : I) -> isProp (isUpperSet (up' i))
    isProp-isUpperSet i = isPropΠⁱ2 (\_ q -> isPropΠ2 (\_ _ -> isProp-U i q))

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
    ; isLowerSet-L = isPropΠ2 (\_ _ -> c.isProp-L _) g1.isLowerSet-L g2.isLowerSet-L i
    ; isUpperSet-U = isPropΠ2 (\_ _ -> c.isProp-U _) g1.isUpperSet-U g2.isUpperSet-U i
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
    i .rightInv (record {}) = refl
    i .leftInv (record {}) = refl

abstract
  isSet-ℝ : isSet ℝ
  isSet-ℝ = subst isSet GoodCut==ℝ isSet-GoodCut
