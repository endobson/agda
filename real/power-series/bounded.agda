{-# OPTIONS --cubical --safe --exact-split #-}

module real.power-series.bounded where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import fin
open import fin.sum-pair
open import finset.instances
open import finset.instances.sum-pair
open import finsum
open import finsum.absolute-value
open import finsum.arithmetic
open import finsum.order
open import functions
open import funext
open import heyting-field.instances.real
open import inhabited.instances.nat
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import nat
open import order
open import order.bound
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field.mean
open import ordered-ring.absolute-value
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.big-o
open import ordered-semiring.big-o.arithmetic
open import ordered-semiring.big-o.common
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.arithmetic.multiplication.inverse
open import real.distance
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.minmax
open import real.sequence.limit.order
open import real.series
open import real.series.big-o
open import real.series.cauchy-product
open import real.series.geometric
open import real.subspace
open import ring
open import ring.exponentiation.diff
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import sequence
open import sequence.partial-sums
open import subset.subspace
open import truncation

private
  module _ (x∈@(x , ax<1) : ∣ℝ∣< 1#)
           (sequences :
             ∀ (y∈@(y , _) : ∣ℝ∣< 1#) ->
               Σ[ s ∈ Sequence ℝ ] (
                 isConvergentSequence s ×
                 ∀ m -> s m ≤ (partial-sums (\n -> distance (x ^ℕ n) (y ^ℕ n)) m)))
           (ε⁺@(ε , 0<ε) : ℝ⁺) where
    private
      xb : ℝ
      xb = mean (abs x) 1#

      ax<xb : abs x < xb
      ax<xb = mean-<₁ ax<1

      axb<1 : abs xb < 1#
      axb<1 = trans-=-< (abs-0≤-path (trans-≤ abs-0≤ (weaken-< ax<xb))) (mean-<₂ ax<1)

      xb∈ : ∣ℝ∣< 1#
      xb∈ = xb , axb<1

      ax∈ : ∣ℝ∣< 1#
      ax∈ = abs x , trans-=-< (abs-0≤-path abs-0≤) ax<1

      glb : ℝ
      glb = geometric-series-limit xb∈

      glax≤glb : geometric-series-limit ax∈ ≤ geometric-series-limit xb∈
      glax≤glb = geometric-series-limit-preserves-≤ ax≤xb
        where
        ax≤xb : abs x ≤ xb
        ax≤xb = weaken-< ax<xb

      0<glb : 0# < glb
      0<glb = geometric-series-limit-0<

      0≤glb : 0# ≤ glb
      0≤glb = weaken-< 0<glb

      1/glb² : ℝ
      1/glb² = ℝ1/ (glb * glb , inj-r (*-preserves-0< 0<glb 0<glb))

      δ' : ℝ
      δ' = ε * 1/glb²
      0<δ' : 0# < δ'
      0<δ' = *-preserves-0< 0<ε (ℝ1/-preserves-0< (*-preserves-0< 0<glb 0<glb))

      δ : ℝ
      δ = min (diff (abs x) xb) δ'
      0<δ : 0# < δ
      0<δ = min-greatest-< (diff-0<⁺ ax<xb) 0<δ'

      module _ (y∈@(y , ay<1) : ∣ℝ∣< 1#) (dxy<δ : distance x y < δ) where

        ay∈ : ∣ℝ∣< 1#
        ay∈ = abs y , trans-=-< (abs-0≤-path abs-0≤) ay<1

        glay≤glb : geometric-series-limit ay∈ ≤ geometric-series-limit xb∈
        glay≤glb = geometric-series-limit-preserves-≤ (weaken-< y<xb)
          where
          daxay< : diff (abs x) (abs y) < diff (abs x) xb
          daxay< = trans-≤-< abs-≤ (trans-≤-< abs-shrinks-distance (trans-<-≤ dxy<δ min-≤-left))
          y<xb : abs y < xb
          y<xb = subst2 _<_ diff-step diff-step (+₁-preserves-< daxay<)

        lt1 : ∀ n -> distance (x ^ℕ (suc n)) (y ^ℕ (suc n)) ≤
                     (abs (diff x y) *
                      finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> (abs x) ^ℕ i * (abs y) ^ℕ j))
        lt1 n =
          trans-=-≤ (cong abs (sym diff*all-ones-path) >=> abs-distrib-*)
            (*₁-preserves-≤
              abs-0≤
              (trans-≤-= finiteSum-abs≤
                (cong finiteSum (funExt (\(fin-pair+ i j _) ->
                  (abs-distrib-* >=> *-cong (abs-^ℕ-path i) (abs-^ℕ-path j)))))))

        p1 : ∀ m -> (partial-sums (\n -> distance (x ^ℕ (suc n)) (y ^ℕ (suc n))) m) ==
                    (partial-sums (\n -> distance (x ^ℕ n) (y ^ℕ n)) (suc m))
        p1 m = sym +-left-zero >=> +-left (sym p1-zero) >=> sym partial-sums-suc
          where
          p1-zero : distance (x ^ℕ 0) (y ^ℕ 0) == 0#
          p1-zero = path->zero-distance (reflᵉ 1#)




        lt2 : ∀ m ->
          (partial-sums (\n -> distance (x ^ℕ n) (y ^ℕ n)) (suc m)) ≤
          (abs (diff x y) *
           (partial-sums (\n ->
             finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> (abs x) ^ℕ i * (abs y) ^ℕ j)) m))
        lt2 m =
          trans-=-≤ (sym (p1 m))
            (trans-≤-= (finiteSum-preserves-≤ (\(n , _) -> lt1 n)) finiteSum-*)


        isLim-pax : isLimit (partial-sums (abs x ^ℕ_)) (geometric-series-limit ax∈)
        isLim-pax = isLimit-geometric-series ax∈
        isLim-pay : isLimit (partial-sums (abs y ^ℕ_)) (geometric-series-limit ay∈)
        isLim-pay = isLimit-geometric-series ay∈

        isLim2 : isLimit
          (\m -> abs (diff x y) * (partial-sums (\n ->
            finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> (abs x) ^ℕ i * (abs y) ^ℕ j)) m))
          (distance x y * (geometric-series-limit ax∈ * geometric-series-limit ay∈))
        isLim2 =
          *₁-preserves-limit
            (isLimit-cauchy-product isLim-pax isLim-pay (isAbsConvergentSeries-geometric-sequence ax∈))

        l2 : ℝ
        l2 = fst (proj₁ (snd (sequences y∈)))

        isLim-l2 : isLimit (fst (sequences y∈)) l2
        isLim-l2 = snd (proj₁ (snd (sequences y∈)))


        lt3 : l2 ≤ (distance x y * (geometric-series-limit ax∈ * geometric-series-limit ay∈))
        lt3 = isLimit-preserves-≤ (dropN-preserves-limit {n = 1} isLim-l2) isLim2
          (\n -> (trans-≤ (proj₂ (snd (sequences y∈)) (suc n)) (lt2 n)))


        lt4 : l2 ≤ (distance x y * (glb * glb))
        lt4 = trans-≤ lt3
          (*₁-preserves-≤ (0≤distanceᵉ x y)
            (trans-≤ (*₁-preserves-≤ (weaken-< geometric-series-limit-0<) glay≤glb)
                     (*₂-preserves-≤ glax≤glb 0≤glb)))

        lt5 : l2 < (δ' * (glb * glb))
        lt5 = trans-≤-< lt4 (*₂-preserves-< (trans-<-≤ dxy<δ min-≤-right) (*-preserves-0< 0<glb 0<glb))
        lt6 : l2 < ε
        lt6 = trans-<-= lt5 (*-assoc >=> *-right ℝ1/-inverse >=> *-right-one)


    opaque
      distance-diff-result :
        Σ[ δ ∈ ℝ⁺ ] ∀ (y∈ : ∣ℝ∣< 1#) -> εClose δ x∈ y∈ -> fst (proj₁ (snd (sequences y∈))) < ε
      distance-diff-result = (δ , 0<δ) , lt6



module _ {f : ℕ -> ℝ} {b : ℝ} (isBound-b : isUpperBound (abs ∘ f) b) where
  private
    0≤b : 0# ≤ b
    0≤b = trans-≤ abs-0≤ (isBound-b 0)

    b' : ℝ
    b' = 1# + b
    b<b' : b < b'
    b<b' = trans-=-< (sym +-left-zero) (+₂-preserves-< 0<1)
    0<b' : 0# < b'
    0<b' = trans-≤-< 0≤b b<b'
    1/b' : ℝ
    1/b' = ℝ1/ (b' , inj-r 0<b')
    0<1/b' : 0# < 1/b'
    0<1/b' = ℝ1/-preserves-0< 0<b'

    1/b'*b<1 : (1/b' * b) < 1#
    1/b'*b<1 = trans-<-= (*₁-preserves-< 0<1/b' b<b') ℝ1/-inverse

  opaque
    isConvergentSeries-Bounded-power-series :
      ∀ ((x , _) : ∣ℝ∣< 1#) -> isConvergentSeries (\i -> f i * x ^ℕ i)
    isConvergentSeries-Bounded-power-series (x , ax<1) =
      isConvergentSeries-BigO bigo
        (isConvergentSeries-geometric-sequence (abs x , (trans-=-< (abs-0≤-path abs-0≤) ax<1)))
      where
      bigo : BigO (\i -> f i * x ^ℕ i) (\i -> (abs x) ^ℕ i)
      bigo =
        subst2 BigO refl
          (funExt (\i -> (*-left-one >=> abs-^ℕ-path i)))
          (BigO-* (BigO-Bounded isBound-b) BigO-abs)

  eval-Bounded-power-series : ∣ℝ∣< 1# -> ℝ
  eval-Bounded-power-series x = fst (isConvergentSeries-Bounded-power-series x)

  isLimit-eval-Bounded-power-series :
    (x∈@(x , _) : ∣ℝ∣< 1#) ->
    isLimit (partial-sums (\i -> f i * x ^ℕ i)) (eval-Bounded-power-series x∈)
  isLimit-eval-Bounded-power-series x = snd (isConvergentSeries-Bounded-power-series x)

  opaque
    isContinuous-eval-Bounded-power-series : isContinuous eval-Bounded-power-series
    isContinuous-eval-Bounded-power-series .isContinuous.at x∈@(x , x<1) ε⁺@(ε , 0<ε) =
      ∣ fst result , (\y∈ close -> *₁-reflects-< (weaken-< 0<1/b') (snd result y∈ close)) ∣
      where
      module _ (y∈@(y , ay<1) : ∣ℝ∣< 1#) where
        seqs : Sequence ℝ
        seqs m = 1/b' * distance (partial-sums (\i -> f i * x ^ℕ i) m)
                                 (partial-sums (\i -> f i * y ^ℕ i) m)

        lim1 : isLimit (\m -> distance (partial-sums (\i -> f i * x ^ℕ i) m)
                                       (partial-sums (\i -> f i * y ^ℕ i) m))
                       (distance (eval-Bounded-power-series x∈) (eval-Bounded-power-series y∈))
        lim1 = abs-preserves-limit (diff-preserves-limit
                (isLimit-eval-Bounded-power-series x∈)
                (isLimit-eval-Bounded-power-series y∈))

        lim2 : isLimit seqs (1/b' * (distance (eval-Bounded-power-series x∈)
                                              (eval-Bounded-power-series y∈)))
        lim2 = *₁-preserves-limit lim1


        module _ (m : Nat) where
          p1 : diff (partial-sums (\i -> f i * x ^ℕ i) m) (partial-sums (\i -> f i * y ^ℕ i) m) ==
               partial-sums (\i -> f i * (diff (x ^ℕ i) (y ^ℕ i))) m
          p1 = sym finiteSum-diff >=>
               cong finiteSum (funExt (\_ -> sym *-distrib-diff-left))
          lt1 : partial-sums (\i -> abs (f i) * (distance (x ^ℕ i) (y ^ℕ i))) m ≤
                (b * partial-sums (\i -> (distance (x ^ℕ i) (y ^ℕ i))) m)
          lt1 = trans-≤-= (finiteSum-preserves-≤ (\(i , _) -> inner-lt1 i)) finiteSum-*
            where
            inner-lt1 : ∀ i -> (abs (f i) * distance (x ^ℕ i) (y ^ℕ i)) ≤
                               (b * distance (x ^ℕ i) (y ^ℕ i))
            inner-lt1 i = *₂-preserves-≤ (isBound-b i) abs-0≤

          lt2 : distance (partial-sums (\i -> f i * x ^ℕ i) m) (partial-sums (\i -> f i * y ^ℕ i) m) ≤
                (b * partial-sums (\i -> (distance (x ^ℕ i) (y ^ℕ i))) m)
          lt2 =
            trans-=-≤ (cong abs p1)
              (trans-≤ finiteSum-abs≤ (trans-=-≤ (cong finiteSum (funExt (\_ -> abs-distrib-*))) lt1))

          lt3 : (1/b' * (distance (partial-sums (\i -> f i * x ^ℕ i) m)
                                    (partial-sums (\i -> f i * y ^ℕ i) m))) ≤
                partial-sums (\i -> (distance (x ^ℕ i) (y ^ℕ i))) m
          lt3 = trans-≤ (*₁-preserves-≤ (weaken-< 0<1/b') lt2)
                  (subst2 _≤_ *-assoc *-left-one
                    (*₂-preserves-≤ (weaken-< 1/b'*b<1)
                                    (finiteSum-preserves-0≤ (\_ -> abs-0≤))))

      result : Σ[ δ ∈ ℝ⁺ ] ∀ (y∈ : ∣ℝ∣< 1#) -> εClose δ x∈ y∈ ->
               (1/b' * (distance (eval-Bounded-power-series x∈)
                                 (eval-Bounded-power-series y∈))) <
               (1/b' * ε)
      result = distance-diff-result x∈ (\y∈ -> seqs y∈ , (_ , lim2 y∈) , lt3 y∈)
                 (1/b' * ε , *-preserves-0< 0<1/b' 0<ε)
