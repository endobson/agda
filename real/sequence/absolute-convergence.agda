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
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
open import real.epsilon-bounded
open import real.sequence.cauchy
open import real.sequence.limit
open import real.series
open import ring.implementations.real
open import semiring
open import sequence
open import sequence.permutation
open import sequence.partial-sums
open import sigma.base
open import subset
open import subset.indicator
open import truncation
open import type-algebra

private
  Seq : Type₁
  Seq = Sequence ℝ

abstract
  AbsConvergentSeries->ConvergentSeries :
    {s : Seq} -> isAbsConvergentSeries s -> isConvergentSeries s
  AbsConvergentSeries->ConvergentSeries {s} isConv =
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
    lt1 = finiteSum-preserves-≤ (\k -> trans-≤-= (*₂-preserves-≤ (indicator-≤1 S' DetS' k) abs-0≤)
                                                  *-left-one)

  permuted-partial-sums-abs-bounded-above :
    {s : Seq} -> (p : Iso ℕ ℕ)  ->
    (∀ i -> Σ[ j ∈ ℕ ] (partial-sums (abs ∘ permute-seq p s) i ≤ partial-sums (abs ∘ s) j))
  permuted-partial-sums-abs-bounded-above {s} p i =
    subst (\s' -> Σ[ j ∈ ℕ ] (partial-sums (abs ∘ permute-seq p s) i ≤ partial-sums (abs ∘ s') j))
          (funExt (\k ii -> s (Iso.rightInv p k ii)))
          (permuted-partial-sums-abs-bounded-below (iso⁻¹ p) i)
