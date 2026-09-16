{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.uniform-limit where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import hlevel
open import metric-space
open import metric-space.cauchy
open import metric-space.ball-subspace
open import metric-space.instances.real
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import order.minmax.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import rational
open import rational.open-interval
open import rational.order
open import real
open import real.arithmetic.rational
open import real.epsilon-bounded hiding (εBounded-diff)
open import real.open-interval
open import real.order
open import ring.implementations.real
open import ordered-semiring.instances.real
open import real.rational
open import real.subspace
open import real.sequence.limit
open import real.sequence.cauchy
open import relation
open import sequence
open import semiring
open import semiring.natural-reciprocal
open import ordered-semiring.natural-reciprocal
open import ordered-semiring
open import sigma.base
open import subset.subspace
open import truncation
open import functions
open import funext


module _ {ℓD : Level} {D : Type ℓD} where

  record isUniformLimit (seq : Sequence (D -> ℝ)) (lim : D -> ℝ) : Type ℓD where
    constructor isUniformLimit-cons
    field
      distance<εℚ :
        ((ε , _) : ℚ⁺) ->
        ∀Largeℕ (\m -> ∀ x -> Real.U (distance (lim x) (seq m x)) ε)

    distance<ε : ((ε , _) : ℝ⁺) -> ∀Largeℕ (\i -> ∀ x -> distance (lim x) (seq i x) < ε)
    distance<ε (ε , 0<ε) = ∥-bind handle 0<ε
      where
      handle : 0# ℝ<' ε -> ∀Largeℕ (\i -> ∀ x -> distance (lim x) (seq i x) < ε)
      handle (ℝ<'-cons q 0Uq εLq) =
        ∀Largeℕ-map (\lt x -> trans-< (U->ℝ< (lt x)) (L->ℝ< εLq))
                    (distance<εℚ (q , U->ℚ< 0Uq))

  isUniformlyConvergent : Pred (Sequence (D -> ℝ)) (ℓ-max ℓ-one ℓD)
  isUniformlyConvergent seq = Σ (D -> ℝ) (isUniformLimit seq)


opaque
  isUniformLimit-∘ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
    {seq : Sequence (B -> ℝ)} {lim : B -> ℝ} ->
    isUniformLimit seq lim -> (f : A -> B) -> isUniformLimit (\i -> seq i ∘ f) (lim ∘ f)
  isUniformLimit-∘ ul f .isUniformLimit.distance<εℚ ε⁺ =
    ∀Largeℕ-map (\d<ε x -> d<ε (f x)) (isUniformLimit.distance<εℚ ul ε⁺)


module _ {ℓD : Level} {D : Type ℓD} {{MD : MetricSpaceStr D}} where

  isLocallyUniformLimit : (Sequence (D -> ℝ)) -> (D -> ℝ) -> Type (ℓ-max ℓD ℓ-one)
  isLocallyUniformLimit seq lim =
    ∀ (x : D) ->
    ∃[ δ ∈ ℝ⁺ ] isUniformLimit (\n -> restrict (seq n) (εBallAtS δ x))
                               (restrict lim (εBallAtS δ x))


  isLocallyUniformlyConvergent : Pred (Sequence (D -> ℝ)) (ℓ-max ℓ-one ℓD)
  isLocallyUniformlyConvergent seq = Σ (D -> ℝ) (isLocallyUniformLimit seq)

  isLocallyUniformlyConvergent' : Pred (Sequence (D -> ℝ)) (ℓ-max ℓ-one ℓD)
  isLocallyUniformlyConvergent' seq =
    ∀ x -> ∃[ δ ∈ ℝ⁺ ] isUniformlyConvergent (\n -> restrict (seq n) (εBallAtS δ x))




module _ {ℓD : Level} {D : Type ℓD} where
  isUniformLimit->isLimit : {s : Sequence (D -> ℝ)} {l : D -> ℝ} ->
    isUniformLimit s l -> ∀ d -> isLimit (\i -> s i d) (l d)
  isUniformLimit->isLimit ul x =
    distance<ε->isLimit
      (\ε -> (∀Largeℕ-map (\d< -> d< x) (isUniformLimit.distance<ε ul ε)))

module _ {ℓD : Level} {D : Type ℓD} {{MD : MetricSpaceStr D}} where

  isUniformLimit->isLocallyUniformLimit : {s : Sequence (D -> ℝ)} {l : D -> ℝ} ->
    isUniformLimit s l -> isLocallyUniformLimit s l
  isUniformLimit->isLocallyUniformLimit ul = \_ -> ∣ (1# , 0<1) , isUniformLimit-∘ ul _ ∣

  isLocallyUniformLimit->isLimit : {s : Sequence (D -> ℝ)} {l : D -> ℝ} ->
    isLocallyUniformLimit s l -> ∀ x -> isLimit (\i -> s i x) (l x)
  isLocallyUniformLimit->isLimit {s} {l} lul x =
    unsquash isProp-isLimit (∥-map handle (lul x))
    where
    handle : Σ[ δ ∈ ℝ⁺ ] isUniformLimit (\i -> restrict (s i) (εBallAtS δ x))
                                        (restrict l (εBallAtS δ x)) ->
             isLimit (\i -> s i x) (l x)
    handle ((d , 0<d) , ul) =
      isUniformLimit->isLimit ul (x , trans-=-< (path->zero-distance (reflᵉ x)) 0<d)



module _ {ℓD : Level} {D : Type ℓD} where
  opaque
    isUniformlyCauchy->isUniformlyConvergent :
      {seq : Sequence (D -> ℝ)} -> isUniformlyCauchy seq -> isUniformlyConvergent seq
    isUniformlyCauchy->isUniformlyConvergent {s} ucauchy = lim , ul
      where
      cauchy : ∀ x -> isCauchy (\i -> s i x)
      cauchy = isUniformlyCauchy->isCauchy ucauchy


      lim : D -> ℝ
      lim x = fst (isCauchy->isConvergentSequence (cauchy x))
      isLim : ∀ x -> isLimit (\i -> s i x) (lim x)
      isLim x = snd (isCauchy->isConvergentSequence (cauchy x))

      ul : isUniformLimit s lim
      ul .isUniformLimit.distance<εℚ (εℚ , 0<εℚ) = ∥-map handle (ucauchy (ε/2 , 0<ε/2))
        where
        ε : ℝ
        ε = ℚ->ℝ εℚ
        ε/2 : ℝ
        ε/2 = ε * 1/2
        0<ε : 0# < ε
        0<ε = ℚ->ℝ-preserves-< 0<εℚ
        0<ε/2 : 0# < ε/2
        0<ε/2 = *-preserves-0< 0<ε 0<1/2
        ε/2⁺ : ℝ⁺
        ε/2⁺ = ε/2 , 0<ε/2

        handle : Σ[ n ∈ Nat ] ((x : D) (m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ -> εClose ε/2⁺ (s m₁ x) (s m₂ x)) ->
                 ∀Largeℕ' (\m -> ∀ x -> Real.U (distance (lim x) (s m x)) εℚ)
        handle (n₁ , close) = n₁ , close'
          where
          close' : ∀ (m : ℕ) -> n₁ ≤ m -> (x : D) -> Real.U (distance (lim x) (s m x)) εℚ
          close' m n₁≤m x =
            unsquash (Real.isProp-U (distance (lim x) (s m x)) εℚ)
                     (∥-map handle2 (isLimit.distance<ε (isLim x) ε/2⁺))
            where
            handle2 : ∀Largeℕ' (\i -> distance (lim x) (s i x) < ε/2) ->
                      Real.U (distance (lim x) (s m x)) εℚ
            handle2 (n₂ , dlim<ε/2) =
              ℝ<->U (trans-<-= (trans-≤-< (distance-triangleᵉ _ _ _)
                                          (+-preserves-< (dlim<ε/2 (max n₂ m) max-≤-left)
                                                         (close x (max n₂ m) m
                                                                  (trans-≤ n₁≤m max-≤-right) n₁≤m)))
                               +-/2-path)

module _ {ℓD : Level} {D : Type ℓD} {{MD : MetricSpaceStr D}} where
  opaque
    private
      isLocallyUniformlyCauchy->isLocallyUniformlyConvergent' :
        {seq : Sequence (D -> ℝ)} ->
        isLocallyUniformlyCauchy seq ->
        isLocallyUniformlyConvergent' seq
      isLocallyUniformlyCauchy->isLocallyUniformlyConvergent' {s} lucauchy x =
        ∥-map (\ (δ , ucauchy) -> (δ , isUniformlyCauchy->isUniformlyConvergent ucauchy))
              (lucauchy x)

    isLocallyUniformlyCauchy->isLocallyUniformlyConvergent :
      {seq : Sequence (D -> ℝ)} ->
      isLocallyUniformlyCauchy seq ->
      isLocallyUniformlyConvergent seq
    isLocallyUniformlyCauchy->isLocallyUniformlyConvergent {s} lucauchy =
      lim , isLULimit
      where
      cauchy : ∀ x -> isCauchy (\i -> s i x)
      cauchy = isLocallyUniformlyCauchy->isCauchy {s = s} lucauchy

      lim : D -> ℝ
      lim x = fst (isCauchy->isConvergentSequence (cauchy x))
      isLim : ∀ x -> isLimit (\i -> s i x) (lim x)
      isLim x = snd (isCauchy->isConvergentSequence (cauchy x))

      isLULimit : isLocallyUniformLimit s lim
      isLULimit x = ∥-map handle (isLocallyUniformlyCauchy->isLocallyUniformlyConvergent' lucauchy x)
        where
        handle : (Σ[ δ ∈ ℝ⁺ ] isUniformlyConvergent (\n -> restrict (s n) (εBallAtS δ x))) ->
                 Σ[ δ ∈ ℝ⁺ ] isUniformLimit (\n -> restrict (s n) (εBallAtS δ x))
                                            (restrict lim (εBallAtS δ x))
        handle (δ , (lim₂ , isULim₂)) = (δ , isULim)
          where
          isLim₂ : ∀ x -> isLimit (\i -> s i (Subspace.value x)) (lim₂ x)
          isLim₂ x = isUniformLimit->isLimit isULim₂ x

          same-lim : ∀ x -> lim₂ x == lim (Subspace.value x)
          same-lim x@(x' , _) =
            cong fst (isProp-isConvergentSequence (lim₂ x , isLim₂ x) (lim x' , isLim x'))

          isULim : isUniformLimit (\n -> restrict (s n) (εBallAtS δ x)) (restrict lim (εBallAtS δ x))
          isULim = subst (isUniformLimit (\n -> restrict (s n) (εBallAtS δ x)))
                         (funExt same-lim)
                         isULim₂
