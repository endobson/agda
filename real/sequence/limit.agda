{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import hlevel
open import nat
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.arithmetic.rational
open import real.epsilon-bounded hiding (εBounded-diff)
open import real.interval
open import real.order
open import real.rational
open import relation
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

  abstract
    close : (i : Iℚ) -> (ℝ∈Iℚ lim i) -> ∀Largeℕ (\m -> ℝ∈Iℚ (seq m) i)
    close (Iℚ-cons l u l≤u) (l<lim , lim<u) =
      ∀Largeℕ-∩ (lower l l<lim) (upper u lim<u)

    lowerℝ : {x : ℝ} -> x < lim -> ∀Largeℕ (\m -> x < (seq m))
    lowerℝ {x} x<lim = ∥-bind handle x<lim
      where
      handle : x ℝ<' lim -> ∀Largeℕ (\m -> x < (seq m))
      handle (ℝ<'-cons q xU-q limL-q) =
        ∀Largeℕ-map (\smL-q -> ∣ ℝ<'-cons q xU-q smL-q ∣) (lower q limL-q)

    upperℝ : {x : ℝ} -> lim < x -> ∀Largeℕ (\m -> (seq m) < x)
    upperℝ {x} lim<x = ∥-bind handle lim<x
      where
      handle : lim ℝ<' x -> ∀Largeℕ (\m -> (seq m) < x)
      handle (ℝ<'-cons q limU-q xL-q) =
        ∀Largeℕ-map (\smU-q -> ∣ ℝ<'-cons q smU-q xL-q ∣) (upper q limU-q)


    εBounded-diff : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff lim (seq i)))
    εBounded-diff ε = ∥-bind handle (find-small-ℝ∈Iℚ lim ε)
      where
      handle : Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ lim qi × i-width qi ≤ ⟨ ε ⟩) ->
               ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff lim (seq i)))
      handle (qi , lim∈qi , wqi≤ε) =
        ∀Largeℕ-map (\{i} si∈qi -> weaken-εBounded wqi≤ε (diff lim (seq i))
                                     (ℝ∈Iℚ->εBounded-diff qi lim (seq i) lim∈qi si∈qi))
                    (close qi lim∈qi)

abstract
  close->isLimit :
    {seq : Seq} {lim : ℝ} ->
    ((i : Iℚ) -> (ℝ∈Iℚ lim i) -> ∀Largeℕ (\m -> ℝ∈Iℚ (seq m) i)) ->
    isLimit seq lim
  close->isLimit {seq} {lim} f .isLimit.lower l L-l = ∥-bind handle (Real.Inhabited-U lim)
    where
    handle : Σ ℚ (Real.U lim) -> ∀Largeℕ (\m -> Real.L (seq m) l)
    handle (u , U-u) = ∀Largeℕ-map proj₁ (f qi (L-l , U-u))
      where
      qi : Iℚ
      qi = ℝ-bounds->Iℚ lim L-l U-u
  close->isLimit {seq} {lim} f .isLimit.upper u U-u = ∥-bind handle (Real.Inhabited-L lim)
    where
    handle : Σ ℚ (Real.L lim) -> ∀Largeℕ (\m -> Real.U (seq m) u)
    handle (l , L-l) = ∀Largeℕ-map proj₂ (f qi (L-l , U-u))
      where
      qi : Iℚ
      qi = ℝ-bounds->Iℚ lim L-l U-u

  isProp-isLimit : {seq : Seq} {lim : ℝ} -> isProp (isLimit seq lim)
  isProp-isLimit l1 l2 i .isLimit.lower q q<v =
    squash (isLimit.lower l1 q q<v) (isLimit.lower l2 q q<v) i
  isProp-isLimit l1 l2 i .isLimit.upper q v<q =
    squash (isLimit.upper l1 q v<q) (isLimit.upper l2 q v<q) i

  εBounded-diff->isLimit :
    {seq : Seq} {lim : ℝ} ->
    ((ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff lim (seq i)))) ->
    isLimit seq lim
  εBounded-diff->isLimit {s} {lim} εB .isLimit.lower l L-l = ∥-bind handle (Real.isUpperOpen-L lim l L-l)
    where
    handle : Σ[ q ∈ ℚ ] (l < q × (Real.L lim q)) -> ∀Largeℕ (\i -> Real.L (s i) l)
    handle (q , l<q , L-q) = ∀Largeℕ-map handle2 (εB (ε , 0<ε))
      where
      ε : ℚ
      ε = diff l q
      0<ε : 0# < ε
      0<ε = diff-0<⁺ l<q
      q<lim : ℚ->ℝ q < lim
      q<lim = L->ℝ< L-q
      handle2 : {i : ℕ} -> εBounded ε (diff lim (s i)) -> Real.L (s i) l
      handle2 {i} (-ε<d' , _) = ℝ<->L lt3
        where
        lt1 : (diff (ℚ->ℝ q) (ℚ->ℝ l)) < diff lim (s i)
        lt1 = trans-=-< (diff-anticommute >=> sym (ℚ->ℝ-preserves-- >=> cong -_ (ℚ->ℝ-preserves-diff)))
                        (L->ℝ< -ε<d')
        lt2 : (ℚ->ℝ q + (diff (ℚ->ℝ q) (ℚ->ℝ l))) < (lim + diff lim (s i))
        lt2 = +-preserves-< q<lim lt1
        lt3 : (ℚ->ℝ l) < (s i)
        lt3 = subst2 _<_ diff-step diff-step lt2
  εBounded-diff->isLimit {s} {lim} εB .isLimit.upper u U-u = ∥-bind handle (Real.isLowerOpen-U lim u U-u)
    where
    handle : Σ[ q ∈ ℚ ] (q < u × (Real.U lim q)) -> ∀Largeℕ (\i -> Real.U (s i) u)
    handle (q , q<u , U-q) = ∀Largeℕ-map handle2 (εB (ε , 0<ε))
      where
      ε : ℚ
      ε = diff q u
      0<ε : 0# < ε
      0<ε = diff-0<⁺ q<u
      lim<q : lim < ℚ->ℝ q
      lim<q = U->ℝ< U-q
      handle2 : {i : ℕ} -> εBounded ε (diff lim (s i)) -> Real.U (s i) u
      handle2 {i} (_ , d'<ε) = ℝ<->U lt3
        where
        lt1 : diff lim (s i) < diff (ℚ->ℝ q) (ℚ->ℝ u)
        lt1 = trans-<-= (U->ℝ< d'<ε) ℚ->ℝ-preserves-diff
        lt2 : (lim + diff lim (s i)) < (ℚ->ℝ q + (diff (ℚ->ℝ q) (ℚ->ℝ u)))
        lt2 = +-preserves-< lim<q lt1
        lt3 : (s i) < (ℚ->ℝ u)
        lt3 = subst2 _<_ diff-step diff-step lt2

isConvergentSequence : Pred Seq ℓ-one
isConvergentSequence s = Σ ℝ (isLimit s)

abstract
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
          module _ where
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
