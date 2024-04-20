{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.absolute-convergence where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.partition
open import finset
open import finset.detachable
open import finset.instances
open import finsum
open import finsum.absolute-value
open import finsum.indicator
open import finsum.order
open import functions
open import funext
open import hlevel
open import isomorphism
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import rational
open import rational.order
open import real
open import real.epsilon-bounded
open import real.order
open import real.sequence.cauchy
open import real.sequence.limit
open import real.series.base
open import ring.implementations.real
open import semiring
open import sequence
open import sequence.partial-sums
open import sequence.permutation
open import sigma
open import sigma.base
open import subset
open import subset.indicator
open import truncation
open import type-algebra

private
  Seq : Type₁
  Seq = Sequence ℝ

abstract
  isAbsConvergentSeries->isConvergentSeries :
    {s : Seq} -> isAbsConvergentSeries s -> isConvergentSeries s
  isAbsConvergentSeries->isConvergentSeries {s} isConv =
    isCauchy->isConvergentSequence
      (\ε -> (∥-map (\{ (n , f) -> ans ε n f }) (isConvergentSequence->isCauchy isConv ε)))
    where
    module _ (ε⁺ : ℚ⁺) (n : ℕ) (f : (m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                                    εBounded ⟨ ε⁺ ⟩ (diff (partial-sums (abs ∘ s) m₁)
                                                     (partial-sums (abs ∘ s) m₂)))
      where
      ε = ⟨ ε⁺ ⟩
      module _ (m1 m2 : Nat) (m1≤m2 : m1 ≤ m2) (n≤m1 : n ≤ m1) (n≤m2 : n ≤ m2) where
         εB-psums-abs : εBounded ε (diff (partial-sums (abs ∘ s) m1) (partial-sums (abs ∘ s) m2))
         εB-psums-abs = f m1 m2 n≤m1 n≤m2

         path1 : (diff (partial-sums (abs ∘ s) m1) (partial-sums (abs ∘ s) m2)) ==
                 (partial-sums (dropN m1 (abs ∘ s)) (fst m1≤m2))
         path1 = diff-partial-sums (abs ∘ s) m1 m2 m1≤m2

         lt1 : abs (partial-sums (dropN m1 s) (fst m1≤m2)) ≤
               (partial-sums (dropN m1 (abs ∘ s)) (fst m1≤m2))
         lt1 = finiteSum-abs≤

         path2 : (diff (partial-sums s m1) (partial-sums s m2)) ==
                 (partial-sums (dropN m1 s) (fst m1≤m2))
         path2 = diff-partial-sums s m1 m2 m1≤m2

         εB-psums : εBounded ε (diff (partial-sums s m1) (partial-sums s m2))
         εB-psums =
           subst (εBounded ε) (sym path2)
             (εBounded-abs≤ lt1 (subst (εBounded ε) path1 εB-psums-abs))

      ans : Σ[ n ∈ ℕ ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                        εBounded ε (diff (partial-sums s m₁) (partial-sums s m₂)))
      ans = n , \m1 m2 n≤m1 n≤m2 -> case (split-< m1 m2) of
                  \{ (inj-l m1<m2) -> εB-psums m1 m2 (weaken-< m1<m2) n≤m1 n≤m2
                   ; (inj-r m2≤m1) ->
                      subst (εBounded ε) (sym diff-anticommute)
                        (εBounded-- _ (εB-psums m2 m1 m2≤m1 n≤m2 n≤m1))
                   }


private
  LateTerm : (N M : ℕ) -> (Subtype (Fin M)) ℓ-zero
  LateTerm N M (k , _) = N ≤ k , isProp-≤

  DetLateTerm : (N M : ℕ) -> Detachable (LateTerm N M)
  DetLateTerm _ _ _ = decide-≤ _ _

  ConvergentSeries->εBounded-LateTerms :
    {s : Seq} -> isConvergentSeries s ->
    (ε : ℚ⁺) ->
    ∃[ N ∈ ℕ ] (∀ n -> N ≤ n ->
                εBounded ⟨ ε ⟩ (finiteSum (\ (k : Fin n) ->
                                 indicator (LateTerm N n) (DetLateTerm N n) k * s (Fin.i k))))
  ConvergentSeries->εBounded-LateTerms {s} (L , isLim) ε⁺@(ε , 0<ε) = εB-dropped-sums
    where
    ε' : ℚ
    ε' = 1/2r * ε
    0<ε' : 0# < ε'
    0<ε' = *-preserves-0< Pos-1/2r 0<ε
    ε'⁺ : ℚ⁺
    ε'⁺ = ε' , 0<ε'
    εB-sums : ∀Largeℕ (\i -> εBounded ε' (diff L (partial-sums s i)))
    εB-sums = isLimit.εBounded-diff isLim ε'⁺

    Ans = Σ[ N ∈ ℕ ] (∀ n -> N ≤ n ->
                      εBounded ε (finiteSum (\ (k : Fin n) ->
                                   indicator (LateTerm N n) (DetLateTerm N n) k * s (Fin.i k))))

    εB-dropped-sums : ∥ Ans ∥
    εB-dropped-sums = ∥-map handle εB-sums
      where
      handle : ∀Largeℕ' (\i -> εBounded ε' (diff L (partial-sums s i))) -> Ans
      handle (N , εB-sums') = N , (\n N≤n -> subst (εBounded ε) (path5 n N≤n) (εB1 n N≤n))
        where

        module _ (n : ℕ) (N≤n : N ≤ n) where
          sums1 : εBounded ε' (diff L (partial-sums s n))
          sums1 = (εB-sums' n N≤n)
          sums2 : εBounded ε' (diff L (partial-sums s N))
          sums2 = (εB-sums' N refl-≤)
          path1 : diff (diff L (partial-sums s N)) (diff L (partial-sums s n)) ==
                  diff (partial-sums s N) (partial-sums s n)
          path1 = +-right (sym diff-anticommute) >=> +-commute >=> diff-trans

          εB1 : εBounded ε (diff (partial-sums s N) (partial-sums s n))
          εB1 = subst2 εBounded (1/2r-path' ε) path1 (εBounded-diff sums2 sums1)

          S : Subtype (Fin n) ℓ-zero
          S = LateTerm N n
          DetS : Detachable S
          DetS = DetLateTerm N n

          instance
            FinSetStr-S : FinSetStr (∈-Subtype S)
            FinSetStr-S .FinSetStr.isFin =
              isFinSet-Detachable S (FinSetStr.isFin useⁱ) DetS

            FinSetStr-¬S : FinSetStr (∉-Subtype S)
            FinSetStr-¬S .FinSetStr.isFin =
              isFinSet-DetachableComp S (FinSetStr.isFin useⁱ) DetS

          ∉S≃FinN : (∉-Subtype S) ≃ Fin N
          ∉S≃FinN = isoToEquiv (iso f g fg gf)
            where
            f : (∉-Subtype S) -> Fin N
            f ((k , k<n) , ¬N≤k) = k , stable-< (¬N≤k ∘ convert-≮)
            g : Fin N -> (∉-Subtype S)
            g (k , k<N) = (k , trans-<-≤ k<N N≤n) , (\N≤k -> convert-≤ N≤k k<N)
            fg : ∀ k -> f (g k) == k
            fg k = fin-i-path refl
            gf : ∀ k -> g (f k) == k
            gf k = ΣProp-path (isProp¬ _) (fin-i-path refl)

          path2 : (partial-sums s n) ==
                  (finiteSum (\ (((k , _) , _) : (∈-Subtype S)) -> s k)) +
                  (finiteSum (\ (((k , _) , _) : (∉-Subtype S)) -> s k))
          path2 = finiteMerge-detachable _ (FinSet-Fin n) S DetS _

          path3 : (finiteSum (\ (((k , _) , _) : (∈-Subtype S)) -> s k)) ==
                  (finiteSum (\ (k : Fin n) -> indicator S DetS k * s (Fin.i k)))
          path3 = finiteSum-indicator S DetS

          path4 : (finiteSum (\ (((k , _) , _) : (∉-Subtype S)) -> s k)) ==
                  partial-sums s N
          path4 = finiteMerge-convert _ (equiv⁻¹ ∉S≃FinN) _

          path5 : (diff (partial-sums s N) (partial-sums s n)) ==
                  (finiteSum (\ (k : Fin n) -> indicator S DetS k * s (Fin.i k)))
          path5 = cong (diff (partial-sums s N)) (path2 >=> +-cong path3 path4) >=>
                  +-assoc >=> +-right +-inverse >=> +-right-zero

  permuted-partial-sums-abs-bounded-below :
    {s : Seq} -> (p : Iso ℕ ℕ)  ->
    (∀ i -> Σ[ j ∈ ℕ ] (partial-sums (abs ∘ s) i ≤ partial-sums (abs ∘ permute-seq p s) j))
  permuted-partial-sums-abs-bounded-below {s} p i =
    j , trans-=-≤ (path2 >=> path3) lt1
    where
    Σlwm : Σ ℕ (isLowWaterMark p i)
    Σlwm = find-LowWaterMark p i
    j = fst Σlwm

    S : Subtype (Fin i) ℓ-zero
    S (k , _) = (Iso.inv p k) < j , isProp-<
    S' : Subtype (Fin j) ℓ-zero
    S' (k , _) = (Iso.fun p k) < i , isProp-<

    DetS : Detachable S
    DetS (k , _) = decide-< _ _
    DetS' : Detachable S'
    DetS' (k , _) = decide-< _ _

    instance
      FinSetStr-S' : FinSetStr (∈-Subtype S')
      FinSetStr-S' .FinSetStr.isFin =
        isFinSet-Detachable S' (FinSetStr.isFin useⁱ) DetS'
      FinSetStr-S : FinSetStr (∈-Subtype S)
      FinSetStr-S .FinSetStr.isFin =
        isFinSet-Detachable S (FinSetStr.isFin useⁱ) DetS

      FinSetStr-¬S : FinSetStr (∉-Subtype S)
      FinSetStr-¬S .FinSetStr.isFin =
        isFinSet-DetachableComp S (FinSetStr.isFin useⁱ) DetS

    isTotal-S : (k : Fin i) -> ⟨ S k ⟩
    isTotal-S (k , k<i) = proj₂ (snd Σlwm) (Iso.inv p k) (trans-=-< (Iso.rightInv p k) k<i)

    Fin-i≃∈S : Fin i ≃ ∈-Subtype S
    Fin-i≃∈S = Σ-isContr-eq (\k -> isTotal-S k , snd (S k) _)

    ∈S≃∈S' : ∈-Subtype S ≃ ∈-Subtype S'
    ∈S≃∈S' = isoToEquiv (iso f g fg gf)
      where
      f : ∈-Subtype S -> ∈-Subtype S'
      f ((k , k<i) , k'<j) = (Iso.inv p k , k'<j) , (trans-=-< (Iso.rightInv p k) k<i)
      g : ∈-Subtype S' -> ∈-Subtype S
      g ((k , k<j) , k'<i) = (Iso.fun p k , k'<i) , (trans-=-< (Iso.leftInv p k) k<j)
      fg : ∀ k -> f (g k) == k
      fg k = ΣProp-path (\{k} -> (snd (S' k))) (fin-i-path (Iso.leftInv p _))
      gf : ∀ k -> g (f k) == k
      gf k = ΣProp-path (\{k} -> (snd (S k))) (fin-i-path (Iso.rightInv p _))

    path2 : finiteSum (\ ((k , _) : Fin i) -> abs (s k)) ==
            finiteSum (\ (((k , _) , _) : (∈-Subtype S')) -> abs (permute-seq p s k))
    path2 = finiteMerge-convert _ (equiv⁻¹ (Fin-i≃∈S >eq> ∈S≃∈S')) _

    path3 : finiteSum (\ (((k , _) , _) : (∈-Subtype S')) -> abs (permute-seq p s k)) ==
            finiteSum (\ (k : Fin j) -> (indicator S' DetS' k * abs (permute-seq p s (Fin.i k))))
    path3 = finiteSum-indicator S' DetS'

    lt1 : finiteSum (\ (k : Fin j) -> (indicator S' DetS' k * abs (permute-seq p s (Fin.i k)))) ≤
          finiteSum (\ (k : Fin j) -> (abs (permute-seq p s (Fin.i k))))
    lt1 = finiteSum-preserves-≤ (\k -> trans-≤-= (*₂-preserves-≤ indicator-≤1 abs-0≤)
                                                  *-left-one)

  permuted-partial-sums-abs-bounded-above :
    {s : Seq} -> (p : Iso ℕ ℕ)  ->
    (∀ i -> Σ[ j ∈ ℕ ] (partial-sums (abs ∘ permute-seq p s) i ≤ partial-sums (abs ∘ s) j))
  permuted-partial-sums-abs-bounded-above {s} p i =
    subst (\s' -> Σ[ j ∈ ℕ ] (partial-sums (abs ∘ permute-seq p s) i ≤ partial-sums (abs ∘ s') j))
          (funExt (\k ii -> s (Iso.rightInv p k ii)))
          (permuted-partial-sums-abs-bounded-below (iso⁻¹ p) i)


  increasing-partial-sums-abs :
    (s : Seq) {i j : ℕ} -> i ≤ j -> partial-sums (abs ∘ s) i ≤ partial-sums (abs ∘ s) j
  increasing-partial-sums-abs s lt = increasing-partial-sums-abs' (≤->≤s lt)
    where
    increasing-partial-sums-abs' :
      {i j : ℕ} -> i ≤s j -> partial-sums (abs ∘ s) i ≤ partial-sums (abs ∘ s) j
    increasing-partial-sums-abs' refl-≤s = refl-≤
    increasing-partial-sums-abs' {i} {suc j} (step-≤s lt) =
      trans-≤ (increasing-partial-sums-abs' lt)
        (trans-=-≤ (sym +-left-zero)
          (trans-≤-= (+₂-preserves-≤ abs-0≤)
            (sym (partial-sums-split (abs ∘ s) j))))

  AbsConvergentSeries->UpperBounded :
    {s : Seq} -> (A : isAbsConvergentSeries s) -> (∀ i -> partial-sums (abs ∘ s) i ≤ ⟨ A ⟩)
  AbsConvergentSeries->UpperBounded {s} (L , isLim) i L<si =
    unsquash isPropBot (∥-map handle (isLimit.upperℝ isLim L<si))
    where
    handle : ∀Largeℕ' (\j -> partial-sums (abs ∘ s) j < partial-sums (abs ∘ s) i) -> Bot
    handle (N , f) = convert-≤ sums-≤ sums-<
      where
      sums-< : partial-sums (abs ∘ s) (max N i) < partial-sums (abs ∘ s) i
      sums-< = f (max N i) max-≤-left
      sums-≤ : partial-sums (abs ∘ s) i ≤ partial-sums (abs ∘ s) (max N i)
      sums-≤ = increasing-partial-sums-abs s max-≤-right


  permute-preserves-limit-partial-sums-abs :
    {s : Seq} -> {l : ℝ} -> (p : Iso ℕ ℕ)  ->
    isLimit (partial-sums (abs ∘ s)) l ->
    isLimit (partial-sums (abs ∘ permute-seq p s)) l
  permute-preserves-limit-partial-sums-abs {s} {l} p isLim = record
    { lower = lower
    ; upper = upper
    }
    where

    lower : ∀ (q : ℚ) -> (Lq : Real.L l q) ->
            ∀Largeℕ (\i -> Real.L (partial-sums (abs ∘ permute-seq p s) i) q)
    lower q Lq = ∥-map handle (isLimit.lower isLim q Lq)
      where
      handle : ∀Largeℕ' (\i -> Real.L (partial-sums (abs ∘ s) i) q) ->
               ∀Largeℕ' (\i -> Real.L (partial-sums (abs ∘ permute-seq p s) i) q)
      handle (N , Lsums) = fst Σj , Lsums'
        where
        Σj : Σ[ j ∈ ℕ ] (partial-sums (abs ∘ s) N ≤ partial-sums (abs ∘ permute-seq p s) j)
        Σj = permuted-partial-sums-abs-bounded-below p N

        Lsums' : ∀ i -> fst Σj ≤ i -> Real.L (partial-sums (abs ∘ permute-seq p s) i) q
        Lsums' i j≤i =
          trans-L-ℝ≤
            (Lsums N refl-≤)
            (trans-≤ (snd Σj) (increasing-partial-sums-abs (permute-seq p s) j≤i))

    upper : ∀ (q : ℚ) -> (Uq : Real.U l q) ->
            ∀Largeℕ (\i -> Real.U (partial-sums (abs ∘ permute-seq p s) i) q)
    upper q Uq = ∣ ans ∣
      where
      Usums : ∀ i -> partial-sums (abs ∘ s) i ≤ l
      Usums = AbsConvergentSeries->UpperBounded (l , isLim)

      ans : ∀Largeℕ' (\i -> Real.U (partial-sums (abs ∘ permute-seq p s) i) q)
      ans = 0 , Usums'
        where
        Usums' : ∀ i -> 0 ≤ i -> Real.U (partial-sums (abs ∘ permute-seq p s) i) q
        Usums' i _ = trans-ℝ≤-U (trans-≤ (snd Σj) (Usums (fst Σj))) Uq
          where
          Σj : Σ[ j ∈ ℕ ] (partial-sums (abs ∘ permute-seq p s) i ≤ partial-sums (abs ∘ s) j)
          Σj = permuted-partial-sums-abs-bounded-above p i

abstract
  permute-preserves-limit-partial-sums :
    {s : Seq} -> {l1 : ℝ} -> (p : Iso ℕ ℕ) ->
    isAbsConvergentSeries s ->
    isLimit (partial-sums s) l1 ->
    isLimit (partial-sums (permute-seq p s)) l1
  permute-preserves-limit-partial-sums {s} {l1} p absConv isLim1 =
    εBounded-diff->isLimit trivial-diff
    where

    module _ (ε⁺ : ℚ⁺) where
      ε = fst ε⁺
      0<ε = snd ε⁺
      ε' : ℚ
      ε' = 1/2r * ε
      0<ε' : 0# < ε'
      0<ε' = *-preserves-0< Pos-1/2r 0<ε
      ε'⁺ : ℚ⁺
      ε'⁺ = ε' , 0<ε'

      trivial-diff : ∀Largeℕ (\n -> (εBounded ε (diff l1 (partial-sums (permute-seq p s) n))))
      trivial-diff = ∥-map2 handle (ConvergentSeries->εBounded-LateTerms absConv ε'⁺)
                                   (isLimit.εBounded-diff isLim1 ε'⁺)
         where
         handle : Σ[ N ∈ ℕ ] (∀ n -> N ≤ n ->
                      εBounded ε' (finiteSum (\ (k : Fin n) ->
                                    indicator (LateTerm N n) (DetLateTerm N n) k * abs (s (Fin.i k))))) ->
                  ∀Largeℕ' (\n -> εBounded ε' (diff l1 (partial-sums s n))) ->
                  ∀Largeℕ' (\n -> (εBounded ε (diff l1 (partial-sums (permute-seq p s) n))))
         handle (N1 , εB-terms) (N2 , εBounded-sums) = M1 , εB3
           where
           N = max N1 N2
           Σlwm : Σ ℕ (isLowWaterMark p N)
           Σlwm = find-LowWaterMark p N
           M1 = fst Σlwm

           module _ (M1' : Nat) (M1≤M1' : M1 ≤ M1') where

             Σlwm' : Σ ℕ (isLowWaterMark (iso⁻¹ p) M1')
             Σlwm' = find-LowWaterMark (iso⁻¹ p) M1'
             M2 = fst Σlwm'

             -- k -> M1 ≤ k -> N ≤ p.fun k
             -- k -> M2 ≤ k -> M1' ≤ p.inv k

             --Remove copy paste

             N≤M2 : N ≤ M2
             N≤M2 = trans-≤-= (proj₁ (snd Σlwm) (Iso.inv p M2)
                                     (trans-≤ M1≤M1' (proj₁ (snd Σlwm') M2 refl-≤)))
                              (Iso.rightInv p M2)

             S1 : Subtype (Fin M1') ℓ-zero
             S1 (k , _) = (Iso.fun p k) < N , isProp-<
             DetS1 : Detachable S1
             DetS1 (k , _) = decide-< _ _

             S2 : Subtype (Fin N) ℓ-zero
             S2 (k , _) = (Iso.inv p k) < M1' , isProp-<
             DetS2 : Detachable S2
             DetS2 (k , _) = decide-< _ _

             S3 : Subtype (Fin M2) ℓ-zero
             S3 (k , _) = ((N ≤ k) × (Iso.inv p k < M1')) , isProp× isProp-≤ isProp-≤
             DetS3 : Detachable S3
             DetS3 = Decidable-∩ (\_ -> decide-≤ _ _) (\_ -> decide-≤ _ _)

             instance
               FinSetStr-S1 : FinSetStr (∈-Subtype S1)
               FinSetStr-S1 .FinSetStr.isFin =
                 isFinSet-Detachable S1 (FinSetStr.isFin useⁱ) DetS1
               FinSetStr-¬S1 : FinSetStr (∉-Subtype S1)
               FinSetStr-¬S1 .FinSetStr.isFin =
                 isFinSet-DetachableComp S1 (FinSetStr.isFin useⁱ) DetS1
               FinSetStr-S2 : FinSetStr (∈-Subtype S2)
               FinSetStr-S2 .FinSetStr.isFin =
                 isFinSet-Detachable S2 (FinSetStr.isFin useⁱ) DetS2
               FinSetStr-S3 : FinSetStr (∈-Subtype S3)
               FinSetStr-S3 .FinSetStr.isFin =
                 isFinSet-Detachable S3 (FinSetStr.isFin useⁱ) DetS3

             eq1 : Fin M1' ≃ (∈-Subtype S1 ⊎ ∉-Subtype S1)
             eq1 = Detachable-eq S1 DetS1

             eq2 : Fin N ≃ ∈-Subtype S2
             eq2 = Σ-isContr-eq (\k -> isTotal-S2 k , snd (S2 k) _)
               where
               isTotal-S2 : (k : Fin N) -> ⟨ S2 k ⟩
               isTotal-S2 (k , k<N) =
                 trans-<-≤ (proj₂ (snd Σlwm) (Iso.inv p k) (trans-=-< (Iso.rightInv p k) k<N))
                           M1≤M1'

             ∉S1≃∈S3 : ∉-Subtype S1 ≃ ∈-Subtype S3
             ∉S1≃∈S3 = isoToEquiv (iso f g fg gf)
               where
               f : ∉-Subtype S1 -> ∈-Subtype S3
               f ((k , k<M1') , k'≮N) =
                 (k' , (proj₂ (snd Σlwm') _ k''<M1')) ,
                 (convert-≮ k'≮N , k''<M1')
                 where
                 k' = Iso.fun p k
                 k''<M1' : Iso.inv p k' < M1'
                 k''<M1' = trans-=-< (Iso.leftInv p k) k<M1'
               g : ∈-Subtype S3 -> ∉-Subtype S1
               g ((k , k<m2) , (N≤k , k'<M1')) =
                 (k' , k'<M1') , convert-≤ (trans-≤-= N≤k (sym (Iso.rightInv p k)))
                 where
                 k' = Iso.inv p k
               fg : ∀ k -> f (g k) == k
               fg k = ΣProp-path (\{k} -> (snd (S3 k))) (fin-i-path (Iso.rightInv p _))
               gf : ∀ k -> g (f k) == k
               gf k = ΣProp-path (isProp¬ _) (fin-i-path (Iso.leftInv p _))


             ∈S2≃∈S1 : ∈-Subtype S2 ≃ ∈-Subtype S1
             ∈S2≃∈S1 = isoToEquiv (iso f g fg gf)
               where
               f : ∈-Subtype S2 -> ∈-Subtype S1
               f ((k , k<i) , k'<j) = (Iso.inv p k , k'<j) , (trans-=-< (Iso.rightInv p k) k<i)
               g : ∈-Subtype S1 -> ∈-Subtype S2
               g ((k , k<j) , k'<i) = (Iso.fun p k , k'<i) , (trans-=-< (Iso.leftInv p k) k<j)
               fg : ∀ k -> f (g k) == k
               fg k = ΣProp-path (\{k} -> (snd (S1 k))) (fin-i-path (Iso.leftInv p _))
               gf : ∀ k -> g (f k) == k
               gf k = ΣProp-path (\{k} -> (snd (S2 k))) (fin-i-path (Iso.rightInv p _))

             path1 : finiteSum (\ ((k , _) : Fin M1') -> (permute-seq p s k)) ==
                     finiteSum (\ (((k , _) , _) : (∈-Subtype S1)) -> (permute-seq p s k)) +
                     finiteSum (\ (((k , _) , _) : (∉-Subtype S1)) -> (permute-seq p s k))
             path1 = finiteMerge-detachable _ (FinSet-Fin M1') S1 DetS1 (permute-seq p s ∘ Fin.i)


             path2 : finiteSum (\ (((k , _) , _) : (∈-Subtype S1)) -> (permute-seq p s k)) ==
                     finiteSum (\ ((k , _) : Fin N) -> (s k))
             path2 = sym (finiteMerge-convert _ (equiv⁻¹ (eq2 >eq> ∈S2≃∈S1)) _)

             path3 : finiteSum (\ (((k , _) , _) : (∉-Subtype S1)) -> (permute-seq p s k)) ==
                     finiteSum (\ (((k , _) , _) : (∈-Subtype S3)) -> (s k))
             path3 = sym (finiteMerge-convert _ ∉S1≃∈S3 _)

             path4 : finiteSum (\ (((k , _) , _) : (∈-Subtype S3)) -> (s k)) ==
                     finiteSum (\ (k : Fin M2) -> indicator S3 DetS3 k * s (Fin.i k))
             path4 = finiteSum-indicator S3 DetS3

             εB1 : εBounded ε' (finiteSum (\ (k : Fin M2) ->
                                 indicator (LateTerm N1 M2) (DetLateTerm N1 M2) k * abs (s (Fin.i k))))
             εB1 = εB-terms M2 (trans-≤ max-≤-left N≤M2)

             lt1 : abs (finiteSum (\ (k : Fin M2) -> indicator S3 DetS3 k * (s (Fin.i k)))) ≤
                       (finiteSum (\ (k : Fin M2) ->
                         indicator (LateTerm N1 M2) (DetLateTerm N1 M2) k * abs (s (Fin.i k))))
             lt1 = trans-≤ finiteSum-abs≤ (finiteSum-preserves-≤ inner-≤)
               where
               S3->LateTerm : (k : Fin M2) -> ⟨ S3 k ⟩ -> ⟨ LateTerm N1 M2 k ⟩
               S3->LateTerm k (N≤k , k'<M1') = trans-≤ max-≤-left N≤k

               ind≤ : (k : Fin M2) -> (abs (indicator S3 DetS3 k)) ≤
                                      (indicator (LateTerm N1 M2) (DetLateTerm N1 M2) k)
               ind≤ k = trans-=-≤ (abs-0≤-path indicator-0≤) (indicator-≤ S3->LateTerm)

               inner-≤ : (k : Fin M2) ->
                 abs (indicator S3 DetS3 k * (s (Fin.i k))) ≤
                 (indicator (LateTerm N1 M2) (DetLateTerm N1 M2) k * abs (s (Fin.i k)))
               inner-≤ k = trans-=-≤ abs-distrib-* (*₂-preserves-≤ (ind≤ k) abs-0≤)

             εB2 : εBounded ε' (finiteSum (\ (k : Fin M2) -> indicator S3 DetS3 k * s (Fin.i k)))
             εB2 = εBounded-abs≤ lt1 εB1

             path5 : (diff l1 (finiteSum (\ ((k , _) : Fin M1') -> (permute-seq p s k)))) ==
                     (diff l1 (finiteSum (\ ((k , _) : Fin N) -> (s k)))) +
                     (finiteSum (\ (k : Fin M2) -> indicator S3 DetS3 k * s (Fin.i k)))
             path5 = cong (diff l1) (path1 >=> +-cong path2 path3 >=> +-commute) >=>
                     +-assoc >=> +-commute >=>
                     +-right path4

             εB3 : εBounded ε (diff l1 (finiteSum (\ ((k , _) : Fin M1') -> (permute-seq p s k))))
             εB3 =
               subst2 εBounded (1/2r-path' ε) (sym path5)
                 (εBounded-+ (diff l1 (finiteSum (\ ((k , _) : Fin N) -> (s k))))
                             (finiteSum (\ (k : Fin M2) -> indicator S3 DetS3 k * s (Fin.i k)))
                             (εBounded-sums N max-≤-right) εB2)

private
  isAbsConvergentSeries-abs :
    {s : Sequence ℝ} ->
    isAbsConvergentSeries s ->
    isAbsConvergentSeries (abs ∘ s)
  isAbsConvergentSeries-abs =
    subst isConvergentSeries (funExt (\i -> sym (abs-0≤-path abs-0≤)))

abstract
  permute-preserves-isAbsConvergentSeries :
    {s : Sequence ℝ} ->
    (p : Iso ℕ ℕ) ->
    isAbsConvergentSeries s ->
    isAbsConvergentSeries (permute-seq p s)
  permute-preserves-isAbsConvergentSeries p (LA , isLimA) =
    (LA , permute-preserves-limit-partial-sums p (isAbsConvergentSeries-abs (LA , isLimA)) isLimA)
