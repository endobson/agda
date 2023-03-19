{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.ratio-test where

open import additive-group
open import additive-group.instances.real
open import additive-group.instances.nat
open import base
open import equality
open import hlevel
open import real
open import nat
open import functions
open import finsum.arithmetic
open import finset.instances
open import funext
open import order
open import order.instances.real
open import order.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import ordered-ring.absolute-value
open import ordered-additive-group.instances.real
open import real.sequence.limit
open import real.series.base
open import real.arithmetic.multiplication.inverse
open import real.rational
open import rational.order
open import rational
open import real.order
open import real.series
open import real.series.geometric
open import real.sequence.absolute-convergence
open import real.sequence.limit.arithmetic
open import ring.implementations.real
open import semiring
open import sum
open import sequence
open import truncation
open import relation

private
  Seq : Type₁
  Seq = Sequence ℝ
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)

private
  _ℝ^ℕ_ : ℝ -> ℕ -> ℝ
  _ℝ^ℕ_ = geometric-sequence

record isRatioSeq (s1 s2 : Seq) : Type₁ where
  field
    f : ∀ n -> s1 n * s2 n == s1 (suc n)

isProp-isRatioSeq : {s1 s2 : Seq} -> isProp (isRatioSeq s1 s2)
isProp-isRatioSeq {s1} {s2} r1 r2 i .isRatioSeq.f =
  isPropΠ (\n -> isSet-ℝ (s1 n * s2 n) (s1 (suc n))) (isRatioSeq.f r1) (isRatioSeq.f r2) i


module _ where
  Archimedean-ℝ' : (ε : ℝ⁺) (x : ℝ) -> 0# ≤ x -> x < 1# -> ∃[ m ∈ ℕ ] (geometric-sequence x m) < ⟨ ε ⟩
  Archimedean-ℝ' (ε , 0<ε) x 0≤x x<1 = ∥-bind2 handle 0<ε x<1
    where
    handle : 0# ℝ<' ε -> x ℝ<' 1# -> ∃[ m ∈ ℕ ] (geometric-sequence x m) < ε
    handle (ℝ<'-cons ε' 0U-ε' εL-ε') (ℝ<'-cons y xU-y 1L-y) =
      ∥-map handle2 (Archimedean-ℚ' (ε' , U->ℚ< 0U-ε') y (weaken-< (U->ℚ< (trans-ℝ≤-U 0≤x xU-y)))
                                    (L->ℚ< 1L-y))
      where
      handle2 : Σ[ m ∈ ℕ ] (y ℚ^ℕ m) < ε' -> Σ[ m ∈ ℕ ] (geometric-sequence x m) < ε
      handle2 (m , y^m<ε') = m ,
        trans-≤-< (trans-≤-= (ℝ^ℕ-preserves-≤ 0≤x (weaken-< (U->ℝ< xU-y)) m)
                             (sym (ℚ^ℕ-ℝ^ℕ-path m)))
                  (trans-< (ℚ->ℝ-preserves-< _ _ y^m<ε') (L->ℝ< εL-ε'))

  -- TODO remove 0≤l argument
  ratio-test : {s1 s2 : Seq} {l : ℝ} -> isRatioSeq s1 s2 -> isLimit (abs ∘ s2) l -> 0# ≤ l -> l < 1# ->
               isAbsConvergentSeries s1
  ratio-test {s1} {s2} {l} isRatio isLim 0≤l l<1 = ans
    where
    module _ (l' : ℝ) (l<l' : l < l') (l'<1 : l' < 1#)
             (l2 : ℝ) (l<l2 : l < l2) (l2<l' : l2 < l') where
      0≤l' : 0# ≤ l'
      0≤l' = trans-≤ 0≤l (weaken-< l<l')
      lowerSeq : Seq
      lowerSeq _ = 0#
      upperSeq : Seq
      upperSeq = (geometric-sequence l')

      isConvergentUpper : isConvergentSeries upperSeq
      isConvergentUpper = isConvergentSeries-geometric-sequence l' 0≤l' l'<1
      isConvergentLower : isConvergentSeries lowerSeq
      isConvergentLower = isConvergentSeries-zero-seq

      lower≤ : ∀Largeℕ (\i -> 0# ≤ abs (s1 i))
      lower≤ = ∣ (0 , \_ _ -> abs-0≤) ∣

      0<l' : 0# < l'
      0<l' = (trans-≤-< 0≤l l<l')
      0<l2 : 0# < l2
      0<l2 = (trans-≤-< 0≤l l<l2)
      0≤l2 : 0# ≤ l2
      0≤l2 = weaken-< 0<l2


      upper≤ : ∀Largeℕ (\i -> abs (s1 i) ≤ upperSeq i)
      upper≤ = ∥-bind handle (isLimit.upperℝ isLim l<l2)
        where
        handle : ∀Largeℕ' (\i -> abs (s2 i) < l2) -> ∀Largeℕ (\i -> abs (s1 i) ≤ upperSeq i)
        handle (n , as2<l2) = p9
          where
          p1 : (m : ℕ) -> (lt : n ≤ m) -> abs (s1 m) ≤ (abs (s1 n) * l2 ℝ^ℕ ⟨ lt ⟩)
          p1 m (zero , path) = path-≤ (cong (abs ∘ s1) (sym path) >=> sym *-right-one)
          p1 zero (suc n , path) = zero-suc-absurd (sym path)
          p1 (suc m) (suc i , path) =
            trans-=-≤
              (cong abs (sym (isRatioSeq.f isRatio m)) >=>
               abs-distrib-*)
              (trans-≤
                (*₂-preserves-≤ (p1 m n≤m) abs-0≤)
                (trans-=-≤
                  *-assoc
                  (*₁-preserves-≤ abs-0≤ (trans-≤ (*₁-preserves-≤ (geometric-sequence-0≤ 0≤l2 i)
                                                                  (weaken-< (as2<l2 m n≤m)))
                                                  (path-≤ *-commute)))))
            where
            n≤m = (i , cong pred path)

          r : ℝ
          r = l2 * (ℝ1/ l' (inj-r 0<l'))
          0<r : 0# < r
          0<r = *-preserves-0< 0<l2 (ℝ1/-preserves-0< l' (inj-r 0<l') 0<l')
          r<1 : r < 1#
          r<1 = trans-<-= (*₂-preserves-< l2<l' (ℝ1/-preserves-0< l' (inj-r 0<l') 0<l'))
                          (*-commute >=> ℝ1/-inverse l' (inj-r 0<l'))
          0≤r : 0# ≤ r
          0≤r = weaken-< 0<r
          r≤1 : r ≤ 1#
          r≤1 = weaken-< r<1

          asn : ℝ
          asn = abs (s1 n)
          ln : ℝ
          ln = (l' ℝ^ℕ n)
          0<ln : 0# < ln
          0<ln = geometric-sequence-0< 0<l' n
          1/ln = ℝ1/ ln (inj-r 0<ln)

          k : ℝ
          k = asn * 1/ln

          l2-r-path : (i : ℕ) -> l2 ℝ^ℕ i == l' ℝ^ℕ i * r ℝ^ℕ i
          l2-r-path i =
            cong (_ℝ^ℕ i) (sym *-right-one >=> *-right (sym (ℝ1/-inverse l' (inj-r 0<l'))) >=>
                           sym *-assoc >=> *-commute) >=>
            (ℝ^ℕ-distrib-*-right i)

          asnl2-path : (m : ℕ) -> (lt : n ≤ m) ->
                       (abs (s1 n) * l2 ℝ^ℕ ⟨ lt ⟩) == (k * r ℝ^ℕ ⟨ lt ⟩) * (l' ℝ^ℕ m)
          asnl2-path m (i , p) =
            *-cong (sym *-right-one >=> *-right (sym (ℝ1/-inverse ln (inj-r 0<ln))) >=>
                    sym *-assoc)
                   (l2-r-path i >=> *-commute) >=>
            *-swap >=>
            *-right (*-commute >=> sym (ℝ^ℕ-distrib-+-left i n) >=>
                     cong (l' ℝ^ℕ_) p)

          p2 : (m : ℕ) -> (lt : n ≤ m) -> abs (s1 m) ≤ ((k * r ℝ^ℕ ⟨ lt ⟩) * (l' ℝ^ℕ m))
          p2 m lt = trans-≤-= (p1 m lt) (asnl2-path m lt)


          module _ (0<k : 0# < k) where
            k-inv = (inj-r 0<k)
            1/k = ℝ1/ k k-inv
            module _ (ri : ℕ) (r< : (r ℝ^ℕ ri) < 1/k) where
              p3 : (m : ℕ) -> (n≤m : n ≤ m) (ri≤i : ri ≤ ⟨ n≤m ⟩) -> (k * r ℝ^ℕ ⟨ n≤m ⟩) < 1#
              p3 m (i , p) ri≤i =
                trans-≤-< (*₁-preserves-≤ (weaken-< 0<k)
                             (geometric-sequence-≤1 (weaken-< 0<r) (weaken-< r<1) _ _ ri≤i))
                          (trans-<-= (*₁-preserves-< 0<k r<) (*-commute >=> ℝ1/-inverse k k-inv))

              p4 : (m : ℕ) -> (ri+n≤m : (ri + n) ≤ m) -> abs (s1 m) ≤ (l' ℝ^ℕ m)
              p4 m (i , p) =
                weaken-<
                  (trans-≤-<
                    (p2 m n≤m)
                    (trans-<-= (*₂-preserves-< (p3 m n≤m ri≤i') (geometric-sequence-0< 0<l' m))
                               *-left-one))
                where
                n≤m : n ≤ m
                n≤m = i + ri , +-assocᵉ i ri n >=> p
                ri≤i' : ri ≤ ⟨ n≤m ⟩
                ri≤i' = i , refl

              p5 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ℝ^ℕ i))
              p5 = ∣ ri + n , p4 ∣

            p6 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ℝ^ℕ i))
            p6 = ∥-bind handle-p6 (Archimedean-ℝ' (1/k , ℝ1/-preserves-0< k k-inv 0<k)
                                                  r (weaken-< 0<r) r<1)
              where
              -- TODO add uncurry and use it here
              handle-p6 : Σ[ m ∈ ℕ ] (geometric-sequence r m) < 1/k ->
                          ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ℝ^ℕ i))
              handle-p6 (i , r^i<1/k) = p5 i r^i<1/k

          module _ (k<1 : k < 1#) where
            p7 : (m : ℕ) -> (lt : n ≤ m) -> abs (s1 m) ≤ (l' ℝ^ℕ m)
            p7 m n≤m@(i , _) =
              weaken-<
                (trans-≤-< (p2 m n≤m)
                  (trans-<-=
                    (*₂-preserves-<
                      (trans-<-≤ (*₂-preserves-< k<1 (geometric-sequence-0< 0<r i))
                                 (trans-=-≤ *-left-one (geometric-sequence-≤1' 0≤r r≤1 i)))
                      (geometric-sequence-0< 0<l' m))
                    *-left-one))
            p8 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ℝ^ℕ i))
            p8 = ∣ n , p7 ∣

          p9 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ℝ^ℕ i))
          p9 = ∥-bind (either p6 p8) (comparison-< _ k _ (ℚ->ℝ-preserves-< _ _ Pos-1r))

      p10 : isAbsConvergentSeries s1
      p10 = squeeze-isConvergentSeries lower≤ upper≤ isConvergentLower isConvergentUpper

    ans : isAbsConvergentSeries s1
    ans =
      unsquash isProp-isConvergentSequence
        (∥-bind (\ (l' , (l<l' , l'<1)) ->
                  (∥-map (\ (l2 , (l<l2 , l2<l')) -> p10 l' l<l' l'<1 l2 l<l2 l2<l')
                         (dense-ℝ< l<l')))
                (dense-ℝ< l<1))
