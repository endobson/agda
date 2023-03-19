{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit.arithmetic where

open import additive-group
open import additive-group.instances.reader
open import additive-group.instances.real
open import base
open import equality
open import nat
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.arithmetic
open import real.interval
open import real.sequence.limit
open import ring
open import ring.solver-equations
open import ring.implementations.real
open import semiring
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
    ε' = 1/2r * ε
    0<ε' = *-preserves-0< Pos-1/2r 0<ε
    f : {m : ℕ} -> (εBounded ε' (diff v1 (s1 m)) × εBounded ε' (diff v2 (s2 m))) ->
                   εBounded ε (diff (v1 + v2) ((s1 m) + (s2 m)))
    f {m} (εB1 , εB2) =
      subst2 εBounded (1/2r-path' ε) +-swap-diff
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
  merge-isLimit : {v1 : ℕ -> ℕ -> ℝ} {v2 : ℕ -> ℝ} {v3 : ℝ} ->
                  isUniformLimit v1 v2 -> isLimit v2 v3 -> isLimit (\i -> v1 i i) v3
  merge-isLimit {v1} {v2} {v3} isLim1 isLim2 = record
    { lower = lower
    ; upper = upper
    }
    where
    lower : (q : ℚ) -> (Real.L v3 q) -> ∀Largeℕ (\m -> Real.L (v1 m m) q)
    lower q v3L-q = ∥-map2 lower' (isLimit.lower isLim2 q v3L-q) (isUniformLimit.lower isLim1 q)
      where
      lower' : ∀Largeℕ' (\i -> Real.L (v2 i) q) ->
               ∀Largeℕ' (\m -> ∀ n -> Real.L (v2 n) q -> Real.L (v1 m n) q) ->
               ∀Largeℕ' (\i -> Real.L (v1 i i) q)
      lower' (N1 , f1) (N2 , f2) =
        max N1 N2 , (\ n N1N2≤n -> f2 n (trans-≤ max-≤-right N1N2≤n)
                                      n (f1 n (trans-≤ max-≤-left N1N2≤n)))

    upper : (q : ℚ) -> (Real.U v3 q) -> ∀Largeℕ (\m -> Real.U (v1 m m) q)
    upper q v3U-q = ∥-map2 upper' (isLimit.upper isLim2 q v3U-q) (isUniformLimit.upper isLim1 q)
      where
      upper' : ∀Largeℕ' (\i -> Real.U (v2 i) q) ->
               ∀Largeℕ' (\m -> ∀ n -> Real.U (v2 n) q -> Real.U (v1 m n) q) ->
               ∀Largeℕ' (\i -> Real.U (v1 i i) q)
      upper' (N1 , f1) (N2 , f2) =
        max N1 N2 , (\ n N1N2≤n -> f2 n (trans-≤ max-≤-right N1N2≤n)
                                      n (f1 n (trans-≤ max-≤-left N1N2≤n)))

  merge-isLimit' : {v1 : ℕ -> ℕ -> ℝ} {v2 : ℕ -> ℝ} {v3 : ℝ} ->
                   isUniformLimit' v1 v2 -> isLimit v2 v3 -> isLimit (\i -> v1 i i) v3
  merge-isLimit' {v1} {v2} {v3} isLim1 isLim2 = εBounded-diff->isLimit εB
    where
    εB : (ε : ℚ⁺) -> ∀Largeℕ (\i -> εBounded ⟨ ε ⟩ (diff v3 (v1 i i)))
    εB (ε , 0<ε) =
      ∀Largeℕ-map (\{i} (fεB , εB) -> subst2 εBounded (1/2r-path' ε) diff-trans
                                             (εBounded-+ _ _ εB (fεB i)))
                  (∀Largeℕ-∩ large1 large2)
      where
      ε' = 1/2r * ε
      0<ε' = *-preserves-0< Pos-1/2r 0<ε
      large1 : ∀Largeℕ (\i -> ∀ a -> εBounded ε' (diff (v2 a) (v1 i a)))
      large1 = isUniformLimit'.εBounded-diff isLim1 (ε' , 0<ε')
      large2 : ∀Largeℕ (\i -> εBounded ε' (diff v3 (v2 i)))
      large2 = isLimit.εBounded-diff isLim2 (ε' , 0<ε')

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
    Σε' : Σ[ ε' ∈ ℚ⁺ ] ((⟨ ε' ⟩ + ⟨ ε' ⟩) + (⟨ ε' ⟩ * ⟨ ε' ⟩)) ≤ ε
    Σε' =
      (ε' , 0<ε') , trans-≤-= (+-preserves-≤ lt-left lt-right) (1/2r-path' ε)
      where
      ε' : ℚ
      ε' = 1/2r * (1/2r * (min ε 1#))
      0<m : 0# < (min ε 1#)
      0<m = (min-greatest-< 0<ε Pos-1r)
      0<ε' : 0# < ε'
      0<ε' = *-preserves-0< Pos-1/2r (*-preserves-0< Pos-1/2r 0<m)
      lt-left : (ε' + ε') ≤ (1/2r * ε)
      lt-left = trans-≤ (path-≤ (1/2r-path' (1/2r * (min ε 1#))))
                        (*₁-preserves-≤ (weaken-< Pos-1/2r) min-≤-left)
      lt-right : (ε' * ε') ≤ (1/2r * ε)
      lt-right = trans-≤ (*₁-preserves-≤ (weaken-< 0<ε') lt1)
                         (*₂-preserves-≤ lt2 (weaken-< 0<ε))
        where
        lt1 : ε' ≤ ε
        lt1 =
          trans-≤-=
            (trans-≤
              (*₂-preserves-≤ (weaken-< 1/2r<1r)
                              (weaken-< (*-preserves-0< Pos-1/2r 0<m)))
              (*₁-preserves-≤ (weaken-< Pos-1r)
                (trans-≤ (weaken-< (trans-<-= (*₂-preserves-< 1/2r<1r 0<m) *-left-one))
                         min-≤-left)))
            *-left-one
        lt2 : ε' ≤ 1/2r
        lt2 =
          trans-≤-=
            (*₁-preserves-≤ (weaken-< Pos-1/2r)
                            (trans-≤ (trans-≤-= (*₁-preserves-≤ (weaken-< Pos-1/2r) min-≤-right)
                                                *-right-one)
                                     (weaken-< 1/2r<1r)))
            *-right-one
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
