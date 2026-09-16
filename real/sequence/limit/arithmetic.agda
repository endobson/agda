{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.arithmetic where

open import additive-group
open import additive-group.instances.reader
open import additive-group.instances.real
open import base
open import equality
open import heyting-field.instances.rational
open import metric-space.uniformly-continuous
open import nat
open import order
open import metric-space
open import metric-space.instances.real
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.rational
open import real.arithmetic
open import real.arithmetic.rational
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.interval
open import real.sequence.limit
open import real.sequence.uniform-limit
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import ring.solver-equations
open import semiring
open import semiring.exponentiation
open import semiring.natural-reciprocal
open import sequence
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

+-preserves-limit : {s1 s2 : Seq} -> {v1 v2 : ℝ} ->
                    isLimit s1 v1 -> isLimit s2 v2 -> isLimit (\i -> s1 i + s2 i) (v1 + v2)
+-preserves-limit {s1} {s2} {v1} {v2} l1 l2 = εBounded-diff->isLimit εB+
  where
  εB1 : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff v1 (s1 i)))
  εB1 = isLimit.εBounded-diff l1
  εB2 : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff v2 (s2 i)))
  εB2 = isLimit.εBounded-diff l2
  εB+ : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff (v1 + v2) ((s1 i) + (s2 i))))
  εB+ (ε , 0<ε) = ∀Largeℕ-map f (∀Largeℕ-∩ (εB1 (ε' , 0<ε')) (εB2 (ε' , 0<ε')))
    where
    ε' = ε * 1/2
    0<ε' = *-preserves-0< 0<ε 0<1/2
    f : {m : ℕ} -> (εBounded ε' (diff v1 (s1 m)) × εBounded ε' (diff v2 (s2 m))) ->
                   εBounded ε (diff (v1 + v2) ((s1 m) + (s2 m)))
    f {m} (εB1 , εB2) =
      subst2 εBounded +-/2-path +-swap-diff
             (εBounded-+ (diff v1 (s1 m)) (diff v2 (s2 m)) εB1 εB2)

minus-preserves-limit : {s : Seq} -> {v : ℝ} ->
                        isLimit s v -> isLimit (\i -> - (s i)) (- v)
minus-preserves-limit {s} {v} l = εBounded-diff->isLimit εB-
  where
  εB : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff v (s i)))
  εB = isLimit.εBounded-diff l
  εB- : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff (- v) (- (s i))))
  εB- (ε , 0<ε) = ∀Largeℕ-map f (εB (ε , 0<ε))
    where
    f : {m : ℕ} -> εBounded ε (diff v (s m)) -> εBounded ε (diff (- v) (- (s m)))
    f {m} εB1 = subst (εBounded ε) minus-distrib-plus (εBounded-- (diff v (s m)) εB1)


diff-preserves-limit : {s1 s2 : Seq} -> {v1 v2 : ℝ} -> isLimit s1 v1 -> isLimit s2 v2 ->
                       isLimit (\i -> diff (s1 i) (s2 i)) (diff v1 v2)
diff-preserves-limit lim1 lim2 = +-preserves-limit lim2 (minus-preserves-limit lim1)


*₁-preserves-limit : {s : Seq} -> {k l : ℝ} ->
                    isLimit s l -> isLimit (\i -> k * s i) (k * l)
*₁-preserves-limit {s} {k} {l} isLim =
  unsquash isProp-isLimit (∥-map handle (∃εBounded k))
  where
  εB : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff l (s i)))
  εB = isLimit.εBounded-diff isLim
  handle : Σ[ ε ∈ ℚ⁺ ] (εBounded ⟨ ε ⟩ k) -> isLimit (\i -> k * s i) (k * l)
  handle ((εk , 0<εk) , εB-k) = εBounded-diff->isLimit εB*
    where
    inv-εk : ℚInv εk
    inv-εk = (\p -> irrefl-path-< (sym p) 0<εk)
    εB* : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff (k * l) (k * (s i))))
    εB* (ε , 0<ε) = ∀Largeℕ-map f (εB (ε' , 0<ε'))
      where
      ε' : ℚ
      ε' = r1/ εk inv-εk * ε
      0<ε' : 0# < ε'
      0<ε' = *-preserves-0< (r1/-preserves-Pos εk inv-εk 0<εk) 0<ε
      f : {m : ℕ} -> εBounded ε' (diff l (s m)) -> εBounded ε (diff (k * l) (k * (s m)))
      f {m} εB-diff =
        subst2 εBounded (sym *-assoc >=> *-left (*-commute >=> r1/-inverse εk inv-εk) >=> *-left-one)
                        (*-distrib-diff-left)
               (εBounded-* k (diff l (s m)) εB-k εB-diff)

*₂-preserves-limit : {s : Seq} -> {k l : ℝ} ->
                    isLimit s l -> isLimit (\i -> s i * k) (l * k)
*₂-preserves-limit {s} {k} {l} isLim =
  transport (\j -> isLimit (\i -> *-commuteᵉ k (s i) j) (*-commuteᵉ k l j))
    (*₁-preserves-limit isLim)

private
  merge-isLimit : {s₁ : ℕ -> ℕ -> ℝ} {s₂ : ℕ -> ℝ} {l : ℝ} ->
                  isUniformLimit s₁ s₂ -> isLimit s₂ l -> isLimit (\i -> s₁ i i) l
  merge-isLimit {s₁} {s₂} {l} isULim-s₁ isLim-s₂ = record
    { lower = lower
    ; upper = upper
    }
    where
    lower : (q : ℚ) -> (Real.L l q) -> ∀Largeℕ (\m -> Real.L (s₁ m m) q)
    lower q lL-q = ∥-bind handle (Real.isUpperOpen-L l q lL-q)
      where
      handle : Σ[ r ∈ ℚ ] (q < r × Real.L l r) ->
               ∀Largeℕ (\m -> Real.L (s₁ m m) q)
      handle (r , q<r , lL-r) =
        ∥-map2 handle2 (isLimit.lower isLim-s₂ r lL-r)
                       (isUniformLimit.distance<εℚ isULim-s₁ (ε , 0<ε))
        where
        ε : ℚ
        ε = diff q r
        0<ε : 0# < ε
        0<ε = diff-0<⁺ q<r

        handle2 : ∀Largeℕ' (\i -> Real.L (s₂ i) r) ->
                  ∀Largeℕ' (\m -> ∀ n -> Real.U (distance (s₂ n) (s₁ m n)) ε) ->
                  ∀Largeℕ' (\i -> Real.L (s₁ i i) q)
        handle2 (N₁ , f₁) (N₂ , f₂) = max N₁ N₂ , close
          where
          close : ∀ i -> (max N₁ N₂) ≤ i -> Real.L (s₁ i i) q
          close i N₁N₂≤i = ℝ<->L lt
            where
            r<s₂i : (ℚ->ℝ r) < (s₂ i)
            r<s₂i = L->ℝ< (f₁ i (trans-≤ max-≤-left N₁N₂≤i))
            d<ε : (distance (s₂ i) (s₁ i i)) < (ℚ->ℝ (diff q r))
            d<ε = U->ℝ< (f₂ i (trans-≤ max-≤-right N₁N₂≤i) i)
            -d₂<ε : (- (diff (s₂ i) (s₁ i i))) < (ℚ->ℝ (diff q r))
            -d₂<ε = trans-≤-< max-≤-right d<ε
            -ε<d₂ : (- (ℚ->ℝ (diff q r))) < (diff (s₂ i) (s₁ i i))
            -ε<d₂ = trans-<-= (minus-flips-< -d₂<ε) minus-double-inverse
            lt : (ℚ->ℝ q) < (s₁ i i)
            lt =
              trans-=-<
                (cong ℚ->ℝ (sym diff-step >=> +-right diff-anticommute) >=> ℚ->ℝ-preserves-diff)
                (trans-<-= (+-preserves-< r<s₂i -ε<d₂) diff-step)

    upper : (q : ℚ) -> (Real.U l q) -> ∀Largeℕ (\m -> Real.U (s₁ m m) q)
    upper q lU-q = ∥-bind handle (Real.isLowerOpen-U l q lU-q)
      where
      handle : Σ[ r ∈ ℚ ] (r < q × Real.U l r) ->
               ∀Largeℕ (\m -> Real.U (s₁ m m) q)
      handle (r , r<q , lU-r) =
        ∥-map2 handle2 (isLimit.upper isLim-s₂ r lU-r)
                       (isUniformLimit.distance<εℚ isULim-s₁ (ε , 0<ε))
        where
        ε : ℚ
        ε = diff r q
        0<ε : 0# < ε
        0<ε = diff-0<⁺ r<q

        handle2 : ∀Largeℕ' (\i -> Real.U (s₂ i) r) ->
                  ∀Largeℕ' (\m -> ∀ n -> Real.U (distance (s₂ n) (s₁ m n)) ε) ->
                  ∀Largeℕ' (\i -> Real.U (s₁ i i) q)
        handle2 (N₁ , f₁) (N₂ , f₂) = max N₁ N₂ , close
          where
          close : ∀ i -> (max N₁ N₂) ≤ i -> Real.U (s₁ i i) q
          close i N₁N₂≤i = ℝ<->U lt
            where
            s₂i<r : (s₂ i) < (ℚ->ℝ r)
            s₂i<r = U->ℝ< (f₁ i (trans-≤ max-≤-left N₁N₂≤i))
            d<ε : (distance (s₂ i) (s₁ i i)) < (ℚ->ℝ (diff r q))
            d<ε = U->ℝ< (f₂ i (trans-≤ max-≤-right N₁N₂≤i) i)
            d₂<ε : (diff (s₂ i) (s₁ i i)) < (ℚ->ℝ (diff r q))
            d₂<ε = trans-≤-< max-≤-left d<ε
            lt : (s₁ i i) < (ℚ->ℝ q)
            lt =
              trans-=-<
                (sym diff-step)
                (trans-<-= (+-preserves-< s₂i<r d₂<ε)
                           (sym ℚ->ℝ-preserves-+ >=> cong ℚ->ℝ diff-step))


*-preserves-limit : {s1 s2 : Seq} -> {v1 v2 : ℝ} ->
                    isLimit s1 v1 -> isLimit s2 v2 -> isLimit (\i -> s1 i * s2 i) (v1 * v2)
*-preserves-limit {s1} {s2} {v1} {v2} l1 l2 = εBounded-diff->isLimit εB*
  where
  εB1 : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff (v1 * v2) (s1 i * v2)))
  εB1 = isLimit.εBounded-diff (*₂-preserves-limit l1)
  εB2 : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff (v1 * v2) (v1 * s2 i)))
  εB2 = isLimit.εBounded-diff (*₁-preserves-limit l2)
  εB3 : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded (⟨ ε ⟩ * ⟨ ε ⟩) ((diff v1 (s1 i)) * (diff v2 (s2 i))))
  εB3 ε = ∀Largeℕ-map (\ (B1 , B2) -> εBounded-* _ _ B1 B2)
            (∀Largeℕ-∩ (isLimit.εBounded-diff l1 ε) (isLimit.εBounded-diff l2 ε))

  εB* : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff (v1 * v2) (s1 i * s2 i)))
  εB* (ε , 0<ε) =
    ∀Largeℕ-map f (∀Largeℕ-∩ (∀Largeℕ-∩ (εB1 ε') (εB2 ε')) (εB3 ε'))
    where
    opaque
      Σε' : Σ[ ε' ∈ ℚ⁺ ] ((⟨ ε' ⟩ + ⟨ ε' ⟩) + (⟨ ε' ⟩ * ⟨ ε' ⟩)) ≤ ε
      Σε' =
        (ε' , 0<ε') , trans-≤-= (+-preserves-≤ lt-left lt-right) +-/2-path
        where
        ε₁ ε₁/2 ε₁/4 ε' : ℚ
        ε₁ = min ε 1#
        ε₁/2 = ε₁ * 1/2
        ε₁/4 = ε₁/2 * 1/2
        ε' = ε₁/4

        0<ε₁ : 0# < ε₁
        0<ε₁ = min-greatest-< 0<ε Pos-1r
        0<ε₁/2 : 0# < ε₁/2
        0<ε₁/2 = *-preserves-0< 0<ε₁ 0<1/2
        0<ε' : 0# < ε'
        0<ε' = *-preserves-0< 0<ε₁/2 0<1/2

        0≤1/2 : 0# ℚ≤ 1/2
        0≤1/2 = weaken-< 0<1/2

        x/2≤x : {x : ℚ} -> 0# ≤ x -> (x * 1/2) ≤ x
        x/2≤x 0≤x =
          trans-≤-= (trans-=-≤ (sym +-right-zero)
                               (+₁-preserves-≤ (*-preserves-0≤ 0≤x 0≤1/2)))
                    +-/2-path
        ε₁/2≤ε₁ : ε₁/2 ≤ ε₁
        ε₁/2≤ε₁ = x/2≤x (weaken-< 0<ε₁)
        ε₁/4≤ε₁/2 : ε₁/4 ≤ ε₁/2
        ε₁/4≤ε₁/2 = x/2≤x (weaken-< 0<ε₁/2)

        lt-left : (ε' + ε') ≤ (ε * 1/2)
        lt-left = trans-=-≤ +-/2-path (*₂-preserves-≤ min-≤-left 0≤1/2)
        lt-right : (ε' * ε') ≤ (ε * 1/2)
        lt-right = trans-≤ (*₂-preserves-≤ lt1 (weaken-< 0<ε'))
                           (*₁-preserves-≤ (weaken-< 0<ε) lt2)
          where
          lt1 : ε' ≤ ε
          lt1 = trans-≤ (trans-≤ ε₁/4≤ε₁/2 ε₁/2≤ε₁) min-≤-left
          lt2 : ε' ≤ 1/2
          lt2 = trans-≤-= (*₂-preserves-≤ (trans-≤ ε₁/2≤ε₁ min-≤-right) 0≤1/2)
                          *-left-one
    ε' = fst Σε'

    d1 : ℕ -> ℝ
    d1 i = (diff (v1 * v2) (s1 i * v2))
    d2 : ℕ -> ℝ
    d2 i = (diff (v1 * v2) (v1 * s2 i))
    d3 : ℕ -> ℝ
    d3 i = ((diff v1 (s1 i)) * (diff v2 (s2 i)))
    f : {i : ℕ} -> ((εBounded ⟨ ε' ⟩ (d1 i) × εBounded ⟨ ε' ⟩ (d2 i)) ×
                    εBounded (⟨ ε' ⟩ * ⟨ ε' ⟩) (d3 i)) ->
                   εBounded ε (diff (v1 * v2) (s1 i * s2 i))
    f {i} ((B1 , B2) , B3) =
      subst (εBounded ε) (sym diff-*-expand)
        (weaken-εBounded (snd Σε') ((d1 i + d2 i) + d3 i)
          (εBounded-+ _ _ (εBounded-+ _ _ B1 B2) B3))


opaque
  ^ℕ-preserves-limit : {s : Seq} -> {v : ℝ} ->
                       isLimit s v -> (n : ℕ) -> isLimit (\i -> s i ^ℕ n) (v ^ℕ n)
  ^ℕ-preserves-limit lim zero = isLimit-constant-seq 1#
  ^ℕ-preserves-limit lim (suc n) =
    *-preserves-limit lim (^ℕ-preserves-limit lim n)
