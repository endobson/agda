{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit where

open import base
open import hlevel
open import nat hiding (_<_)
open import rational
open import rational.proper-interval
open import real
open import real.order
open import real.interval
open import relation
open import order
open import order.instances.rational
open import order.instances.nat
open import sequence
open import sigma.base
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

record isLimit (seq : Seq) (lim : ℝ) : Type ℓ-one where
  no-eta-equality
  field
    lower : (q : ℚ) -> (Real.L lim q) -> ∀Largeℕ (\m -> Real.L (seq m) q)
    upper : (q : ℚ) -> (Real.U lim q) -> ∀Largeℕ (\m -> Real.U (seq m) q)

  close : (i : Iℚ) -> (ℝ∈Iℚ lim i) -> ∀Largeℕ (\m -> ℝ∈Iℚ (seq m) i)
  close (Iℚ-cons l u l≤u) (l<lim , lim<u) =
    ∀Largeℕ-∩ (lower l l<lim) (upper u lim<u)

close->isLimit :
  {seq : Seq} {lim : ℝ} ->
  ((i : Iℚ) -> (ℝ∈Iℚ lim i) -> ∀Largeℕ (\m -> ℝ∈Iℚ (seq m) i)) ->
  isLimit seq lim
close->isLimit {seq} {lim} f .isLimit.lower l L-l = ∥-bind handle (Real.Inhabited-U lim)
  where
  handle : Σ ℚ (Real.U lim) -> ∀Largeℕ (\m -> Real.L (seq m) l)
  handle (u , U-u) = ∀Largeℕ-map proj₁ (f qi (L-l , U-u))
    where
    qi = ℝ-bounds->Iℚ lim L-l U-u
close->isLimit {seq} {lim} f .isLimit.upper u U-u = ∥-bind handle (Real.Inhabited-L lim)
  where
  handle : Σ ℚ (Real.L lim) -> ∀Largeℕ (\m -> Real.U (seq m) u)
  handle (l , L-l) = ∀Largeℕ-map proj₂ (f qi (L-l , U-u))
    where
    qi = ℝ-bounds->Iℚ lim L-l U-u

isProp-isLimit : {seq : Seq} {lim : ℝ} -> isProp (isLimit seq lim)
isProp-isLimit l1 l2 i .isLimit.lower q q<v =
  squash (isLimit.lower l1 q q<v) (isLimit.lower l2 q q<v) i
isProp-isLimit l1 l2 i .isLimit.upper q v<q =
  squash (isLimit.upper l1 q v<q) (isLimit.upper l2 q v<q) i

isConvergentSequence : Pred Seq ℓ-one
isConvergentSequence s = Σ ℝ (isLimit s)

isProp-isConvergentSequence : {s : Seq} -> isProp (isConvergentSequence s)
isProp-isConvergentSequence {seq} (v1 , lim1) (v2 , lim2) = ΣProp-path isProp-isLimit v1=v2
  where
  v1=v2 : v1 == v2
  v1=v2 = overlapping-ℝ∈Iℚs->path v1 v2 f
    where
    f : (qi1 qi2 : Iℚ) -> (ℝ∈Iℚ v1 qi1) -> (ℝ∈Iℚ v2 qi2) -> Overlap qi1 qi2
    f qi1@(Iℚ-cons l1 u1 _) qi2@(Iℚ-cons l2 u2 _) (l1<v1 , v1<u1) (l2<v2 , v2<u2) =
      handle (split-Overlap qi1 qi2)
      where
      handle2 : {l u : ℚ} -> u < l ->
                ∀Largeℕ' (\m -> Real.L (seq m) l) ->
                ∀Largeℕ' (\m -> Real.U (seq m) u) ->
                Bot
      handle2 {l} {u} u<l ∀Lℕ-l ∀Lℕ-u =
        asym-< u<l (ℝ-bounds->ℚ< (seq n) (proj₁ (LU n refl-≤)) (proj₂ (LU n refl-≤)))
        where
        ∀Lℕ = (∀Largeℕ'-∩ ∀Lℕ-l ∀Lℕ-u)
        n = fst ∀Lℕ
        LU = snd ∀Lℕ

      handle : (Overlap qi1 qi2 ⊎ NonOverlap qi1 qi2) -> Overlap qi1 qi2
      handle (inj-l over) = over
      handle (inj-r (inj-l u1<l2)) =
        bot-elim (unsquash isPropBot
                   (∥-map2 (handle2 u1<l2) (isLimit.lower lim2 l2 l2<v2)
                                           (isLimit.upper lim1 u1 v1<u1)))
      handle (inj-r (inj-r u2<l1)) =
        bot-elim (unsquash isPropBot
                   (∥-map2 (handle2 u2<l1) (isLimit.lower lim1 l1 l1<v1)
                                           (isLimit.upper lim2 u2 v2<u2)))
