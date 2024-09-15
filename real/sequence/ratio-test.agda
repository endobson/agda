{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.ratio-test where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import finset.instances
open import finsum.arithmetic
open import functions
open import funext
open import hlevel
open import nat
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.exponentiation
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import rational
open import rational.order
open import real
open import real.arithmetic.multiplication.inverse
open import real.order
open import real.rational
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.series
open import real.series.base
open import real.series.geometric
open import real.subspace
open import relation
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import sequence
open import subset.subspace
open import sum
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

record isRatioSeq (s1 s2 : Seq) : Type₁ where
  field
    f : ∀ n -> s1 n * s2 n == s1 (suc n)

isProp-isRatioSeq : {s1 s2 : Seq} -> isProp (isRatioSeq s1 s2)
isProp-isRatioSeq {s1} {s2} r1 r2 i .isRatioSeq.f =
  isPropΠ (\n -> isSet-ℝ (s1 n * s2 n) (s1 (suc n))) (isRatioSeq.f r1) (isRatioSeq.f r2) i


module _ where
  Archimedean-ℝ' : ((ε , _) : ℝ⁺) (x : ℝ) -> 0# ≤ x -> x < 1# ->
                   ∃[ m ∈ ℕ ] (geometric-sequence x m) < ε
  Archimedean-ℝ' (ε , 0<ε) x 0≤x x<1 = ∥-bind2 handle 0<ε x<1
    where
    handle : 0# ℝ<' ε -> x ℝ<' 1# -> ∃[ m ∈ ℕ ] (geometric-sequence x m) < ε
    handle (ℝ<'-cons ε' 0U-ε' εL-ε') (ℝ<'-cons y xU-y 1L-y) =
      ∥-map handle2 (Archimedean-ℚ' (ε' , U->ℚ< 0U-ε') y (weaken-< (U->ℚ< (trans-ℝ≤-U 0≤x xU-y)))
                                    (L->ℚ< 1L-y))
      where
      handle2 : Σ[ m ∈ ℕ ] (y ^ℕ m) < ε' -> Σ[ m ∈ ℕ ] (geometric-sequence x m) < ε
      handle2 (m , y^m<ε') = m ,
        trans-≤-< (trans-≤-= (^ℕ-0≤-preserves-≤ 0≤x m (weaken-< (U->ℝ< xU-y)))
                             (sym (ℚ^ℕ-ℝ^ℕ-path m)))
                  (trans-< (ℚ->ℝ-preserves-< y^m<ε') (L->ℝ< εL-ε'))

  ratio-test : {s1 s2 : Seq} ((l , _) : ∣ℝ∣< 1#) -> isRatioSeq s1 s2 -> isLimit (abs ∘ s2) l ->
               isAbsConvergentSeries s1
  ratio-test {s1} {s2} (l , al<1) isRatio isLim = ans
    where
    module _ (l' : ℝ) (al<l' : abs l < l') (l'<1 : l' < 1#)
             (l2 : ℝ) (al<l2 : abs l < l2) (l2<l' : l2 < l') where
      0≤l' : 0# ≤ l'
      0≤l' = trans-≤ abs-0≤ (weaken-< al<l')
      lowerSeq : Seq
      lowerSeq _ = 0#
      upperSeq : Seq
      upperSeq = (geometric-sequence l')

      isConvergentUpper : isConvergentSeries upperSeq
      isConvergentUpper =
        isConvergentSeries-geometric-sequence (l' , (trans-=-< (abs-0≤-path 0≤l') l'<1))
      isConvergentLower : isConvergentSeries lowerSeq
      isConvergentLower = isConvergentSeries-zero-seq

      lower≤ : ∀Largeℕ (\i -> 0# ≤ abs (s1 i))
      lower≤ = ∣ (0 , \_ _ -> abs-0≤) ∣

      0<l' : 0# < l'
      0<l' = (trans-≤-< abs-0≤ al<l')
      0<l2 : 0# < l2
      0<l2 = (trans-≤-< abs-0≤ al<l2)
      0≤l2 : 0# ≤ l2
      0≤l2 = weaken-< 0<l2


      upper≤ : ∀Largeℕ (\i -> abs (s1 i) ≤ upperSeq i)
      upper≤ = ∥-bind handle (isLimit.upperℝ isLim (trans-≤-< abs-≤ al<l2))
        where
        handle : ∀Largeℕ' (\i -> abs (s2 i) < l2) -> ∀Largeℕ (\i -> abs (s1 i) ≤ upperSeq i)
        handle (n , as2<l2) = p9
          where
          p1 : (m : ℕ) -> (lt : n ≤ m) -> abs (s1 m) ≤ (abs (s1 n) * l2 ^ℕ ⟨ lt ⟩)
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
          r = l2 * (ℝ1/ (l' , (inj-r 0<l')))
          0<r : 0# < r
          0<r = *-preserves-0< 0<l2 (ℝ1/-preserves-0< 0<l')
          r<1 : r < 1#
          r<1 = trans-<-= (*₂-preserves-< l2<l' (ℝ1/-preserves-0< 0<l'))
                          (*-commute >=> ℝ1/-inverse)
          0≤r : 0# ≤ r
          0≤r = weaken-< 0<r
          r≤1 : r ≤ 1#
          r≤1 = weaken-< r<1

          asn : ℝ
          asn = abs (s1 n)
          ln : ℝ
          ln = (l' ^ℕ n)
          0<ln : 0# < ln
          0<ln = geometric-sequence-0< 0<l' n
          1/ln = ℝ1/ (ln , (inj-r 0<ln))

          k : ℝ
          k = asn * 1/ln

          l2-r-path : (i : ℕ) -> l2 ^ℕ i == l' ^ℕ i * r ^ℕ i
          l2-r-path i =
            cong (_^ℕ i) (sym *-right-one >=> *-right (sym ℝ1/-inverse) >=>
                          sym *-assoc >=> *-commute) >=>
            (^ℕ-distrib-*-right i)

          asnl2-path : (m : ℕ) -> (lt : n ≤ m) ->
                       (abs (s1 n) * l2 ^ℕ ⟨ lt ⟩) == (k * r ^ℕ ⟨ lt ⟩) * (l' ^ℕ m)
          asnl2-path m (i , p) =
            *-cong (sym *-right-one >=> *-right (sym ℝ1/-inverse) >=>
                    sym *-assoc)
                   (l2-r-path i >=> *-commute) >=>
            *-swap >=>
            *-right (*-commute >=> sym (^ℕ-distrib-+-left i n) >=>
                     cong (l' ^ℕ_) p)

          p2 : (m : ℕ) -> (lt : n ≤ m) -> abs (s1 m) ≤ ((k * r ^ℕ ⟨ lt ⟩) * (l' ^ℕ m))
          p2 m lt = trans-≤-= (p1 m lt) (asnl2-path m lt)


          module _ (0<k : 0# < k) where
            1/k = ℝ1/ (k , (inj-r 0<k))
            module _ (ri : ℕ) (r< : (r ^ℕ ri) < 1/k) where
              p3 : (m : ℕ) -> (n≤m : n ≤ m) (ri≤i : ri ≤ ⟨ n≤m ⟩) -> (k * r ^ℕ ⟨ n≤m ⟩) < 1#
              p3 m (i , p) ri≤i =
                trans-≤-< (*₁-preserves-≤ (weaken-< 0<k)
                             (geometric-sequence-≤1 (weaken-< 0<r) (weaken-< r<1) _ _ ri≤i))
                          (trans-<-= (*₁-preserves-< 0<k r<) (*-commute >=> ℝ1/-inverse))

              p4 : (m : ℕ) -> (ri+n≤m : (ri + n) ≤ m) -> abs (s1 m) ≤ (l' ^ℕ m)
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

              p5 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ^ℕ i))
              p5 = ∣ ri + n , p4 ∣

            p6 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ^ℕ i))
            p6 = ∥-bind handle-p6 (Archimedean-ℝ' (1/k , ℝ1/-preserves-0< 0<k)
                                                  r (weaken-< 0<r) r<1)
              where
              -- TODO add uncurry and use it here
              handle-p6 : Σ[ m ∈ ℕ ] (geometric-sequence r m) < 1/k ->
                          ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ^ℕ i))
              handle-p6 (i , r^i<1/k) = p5 i r^i<1/k

          module _ (k<1 : k < 1#) where
            p7 : (m : ℕ) -> (lt : n ≤ m) -> abs (s1 m) ≤ (l' ^ℕ m)
            p7 m n≤m@(i , _) =
              weaken-<
                (trans-≤-< (p2 m n≤m)
                  (trans-<-=
                    (*₂-preserves-<
                      (trans-<-≤ (*₂-preserves-< k<1 (geometric-sequence-0< 0<r i))
                                 (trans-=-≤ *-left-one (geometric-sequence-≤1' 0≤r r≤1 i)))
                      (geometric-sequence-0< 0<l' m))
                    *-left-one))
            p8 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ^ℕ i))
            p8 = ∣ n , p7 ∣

          p9 : ∀Largeℕ (\i -> abs (s1 i) ≤ (l' ^ℕ i))
          p9 = ∥-bind (either p6 p8) (comparison-< _ k _ (ℚ->ℝ-preserves-< Pos-1r))

      p10 : isAbsConvergentSeries s1
      p10 = squeeze-isConvergentSeries lower≤ upper≤ isConvergentLower isConvergentUpper

    ans : isAbsConvergentSeries s1
    ans =
      unsquash isProp-isConvergentSequence
        (∥-bind (\ (l' , (al<l' , l'<1)) ->
                  (∥-map (\ (l2 , (al<l2 , l2<l')) -> p10 l' al<l' l'<1 l2 al<l2 l2<l')
                         (dense-ℝ< al<l')))
                (dense-ℝ< al<1))
