{-# OPTIONS --cubical --safe --exact-split #-}

module real.infinite-sum.triangle where


open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import combinatorics.triangle-numbers
open import cubical
open import decision
open import equality-path
open import equivalence
open import equivalence.base
open import fin.sum-pair
open import functions
open import functions.embedding
open import funext
open import hlevel.base
open import hlevel.sigma
open import isomorphism
open import nat
open import finset
open import finset.instances
open import finset.instances.sigma
open import finset.instances.sum-pair
open import nat.iteration
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import real
open import commutative-monoid
open import finite-commutative-monoid
open import finite-commutative-monoid.sigma
open import real.infinite-sum
open import real.sequence.absolute-convergence
open import real.sequence.limit
open import real.sequence.limit.order
open import real.sequence.limit.subsequence
open import real.series
open import real.series.base
open import real.series.cauchy-product
open import relation
open import ring.implementations.real
open import semiring
open import sequence
open import sequence.partial-sums
open import sequence.subsequence
open import sigma
open import fin
open import finset.injective
open import finsum
open import finsum.cardinality
open import sigma.base
open import truncation


private
  MaxTri≤ : ℕ -> Type₀
  MaxTri≤ n = Σ[ n₀ ∈ ℕ ] (isTriangleNumber n₀ × (n₀ ≤ n) × (∀ i -> n₀ < i -> i ≤ n -> ¬ (isTriangleNumber i)))

  compute-MaxTri≤ : ∀ n -> MaxTri≤ n
  compute-MaxTri≤ n = rec n refl-≤ base-larger
    where
    base-larger : ∀ i -> n < i -> i ≤ n -> ¬ (isTriangleNumber i)
    base-larger i n<i i≤n _ = convert-≤ i≤n n<i

    rec : (n₀ : ℕ) -> n₀ ≤ n -> (∀ i -> n₀ < i -> i ≤ n -> ¬ (isTriangleNumber i)) -> MaxTri≤ n
    rec zero _ larger = zero , isTriangleNumber-zero , zero-≤ , larger
    rec (suc n₀) sn₀≤n larger = handle (decide-isTriangleNumber (suc n₀))
      where
      handle : Dec (isTriangleNumber (suc n₀)) -> MaxTri≤ n
      handle (yes t) = suc n₀ , t , sn₀≤n , larger
      handle (no ¬t) = rec n₀ (weaken-< sn₀≤n) larger'
        where
        larger' : ∀ i -> n₀ < i -> i ≤ n -> ¬ (isTriangleNumber i)
        larger' i sn₀≤i i≤n = handle₂ (split-< (suc n₀) i)
          where
          handle₂ : (suc n₀ < i) ⊎ (i ≤ suc n₀) -> ¬ (isTriangleNumber i)
          handle₂ (inj-l sn₀<i) = larger i sn₀<i i≤n
          handle₂ (inj-r i≤sn₀) =
            subst (¬ ∘ isTriangleNumber) (antisym-≤ sn₀≤i i≤sn₀) ¬t


  isProp-MaxTri≤ : ∀ n -> isProp (MaxTri≤ n)
  isProp-MaxTri≤ m (n₁ , p₁@(t₁ , n₁≤m , larger₁))
                   (n₂ , p₂@(t₂ , n₂≤m , larger₂)) =
    \k -> pn k , pp k
    where
    pn : n₁ == n₂
    pn = case (trichotomous-< n₁ n₂) of
      (\{ (tri< n₁<n₂ _ _) -> bot-elim (larger₁ n₂ n₁<n₂ n₂≤m t₂)
        ; (tri= _ n₁=n₂ _) -> n₁=n₂
        ; (tri> _ _ n₂<n₁) -> bot-elim (larger₂ n₁ n₂<n₁ n₁≤m t₁)
        })

    pp : PathP (\k -> (isTriangleNumber (pn k) × ((pn k) ≤ m) ×
                      (∀ i -> (pn k) < i -> i ≤ m -> ¬ (isTriangleNumber i))))
               p₁ p₂
    pp = isProp->PathP (\k ->
      isProp× (isProp-isTriangleNumber (pn k) )
        (isProp× isProp-≤
                 (isPropΠ4 (\_ _ _ _ -> isPropBot))))

  ΣMaxTri≤->ℕ : Σ[ n ∈ ℕ ] (MaxTri≤ n) -> ℕ
  ΣMaxTri≤->ℕ (n , p) = n

  ℕ->ΣMaxTri≤ : ℕ -> Σ[ n ∈ ℕ ] (MaxTri≤ n)
  ℕ->ΣMaxTri≤ n = n , compute-MaxTri≤ n


  ΣMaxTri≤-ℕ-Iso : Iso (Σ[ n ∈ ℕ ] (MaxTri≤ n)) ℕ
  ΣMaxTri≤-ℕ-Iso = iso ΣMaxTri≤->ℕ ℕ->ΣMaxTri≤ (\_ -> refl) bf
    where
    bf : ∀ mt -> ℕ->ΣMaxTri≤ (ΣMaxTri≤->ℕ mt) == mt
    bf _ = ΣProp-path (isProp-MaxTri≤ _) refl


  ΣMaxTri≤->ℕ×ℕ : Σ[ n ∈ ℕ ] (MaxTri≤ n) -> ℕ × ℕ
  ΣMaxTri≤->ℕ×ℕ (n , (n₀ , (i , pi) , (d , pd) , ¬larger)) = i -' d , d

  ℕ×ℕ->ΣMaxTri≤ : ℕ × ℕ -> Σ[ n ∈ ℕ ] (MaxTri≤ n)
  ℕ×ℕ->ΣMaxTri≤ (i , j) =
    (j + triangle-number (i + j) ,
     triangle-number (i + j) ,
     (i + j , refl) ,
     (j , refl) ,
     larger)
    where
    larger : ∀ k ->
             (triangle-number (i + j) < k) ->
             (k ≤ (j + triangle-number (i + j))) ->
             ¬ (isTriangleNumber k)
    larger k n₀<k k≤n (ki , p) = handle (split-< (i + j) ki)
      where
      handle : ¬ (((i + j) < ki) ⊎ (ki ≤ (i + j)))
      handle (inj-r ki≤i+j) =
        irrefl-< (trans-<-≤ n₀<k (trans-=-≤ (sym p) (triangle-number-preserves-≤ ki≤i+j)))
      handle (inj-l i+j<ki) = convert-≤ tsij≤k k<tsij
        where
        opaque
          unfolding triangle-number
          tsij≤k : (suc (i + j) + triangle-number (i + j)) ≤ k
          tsij≤k = trans-≤-= (triangle-number-preserves-≤ i+j<ki) p
          j<sij : j < suc (i + j)
          j<sij = suc-≤ (i , refl)
          k<tsij : k < (suc (i + j) + triangle-number (i + j))
          k<tsij = trans-≤-< k≤n (+₂-preserves-< j<sij)


  ℕ×ℕ-ΣMaxTri≤-Iso : Iso (ℕ × ℕ) (Σ[ n ∈ ℕ ] (MaxTri≤ n))
  ℕ×ℕ-ΣMaxTri≤-Iso = iso ℕ×ℕ->ΣMaxTri≤ ΣMaxTri≤->ℕ×ℕ fb bf
    where
    fb : ∀ mt -> ℕ×ℕ->ΣMaxTri≤ (ΣMaxTri≤->ℕ×ℕ mt) == mt
    fb (n , mt@(n₀ , (i , pi) , (d , pd) , ¬larger)) = \i -> pn i , pmt i
      where
      n₂ : ℕ
      n₂ = (d + triangle-number ((i -' d) + d))
      mt₂ : MaxTri≤ n₂
      mt₂ = snd (ℕ×ℕ->ΣMaxTri≤ (ΣMaxTri≤->ℕ×ℕ (n , mt)))

      pn : n₂ == n
      pn = cong (d +_) (cong triangle-number (handle-d≤i d≤i) >=> pi) >=> pd
        where
        d≤i : d ≤ i
        d≤i = convert-≮ i≮d
          where
          opaque
            unfolding triangle-number
            i≮d : i ≮ d
            i≮d i<d = ¬larger t n₀<t t≤n isTriangleNumber-t
              where
              t : ℕ
              t = suc i + n₀

              n₀<t : n₀ < t
              n₀<t = +₂-preserves-< zero-<

              t≤n : t ≤ n
              t≤n = trans-≤-= (+₂-preserves-≤ i<d) pd

              isTriangleNumber-t : isTriangleNumber t
              isTriangleNumber-t = (suc i) , cong (suc i +_) pi

        handle-d≤i : (d ≤ i) -> ((i -' d) + d) == i
        handle-d≤i (j , j+d=i) =
          (\k -> (j+d=i (~ k) -' d) + d) >=>
          cong (_+ d) (+'-minus-right d) >=>
          j+d=i


      pmt : PathP (\i -> MaxTri≤ (pn i)) mt₂ mt
      pmt = isProp->PathP (\i -> isProp-MaxTri≤ (pn i))

    bf : ∀ ij -> ΣMaxTri≤->ℕ×ℕ (ℕ×ℕ->ΣMaxTri≤ ij) == ij
    bf (i , j) k = +'-minus-right {i} j k , j


triangle-encode : (ℕ × ℕ) -> ℕ
triangle-encode (i , j) = j + triangle-number (i + j)

opaque
  isEquiv-triangle-encode : isEquiv triangle-encode
  isEquiv-triangle-encode =
    snd (isoToEquiv (ℕ×ℕ-ΣMaxTri≤-Iso >iso> ΣMaxTri≤-ℕ-Iso))



module _ (t : ℕ) where
  -- TriFin->ΣFinPair : Fin (triangle-number t) -> Σ[ (i , _) ∈ Fin t ] (FinPair+ i)
  -- TriFin->ΣFinPair (i , i<T) = ?


  ΣFinPair->TriFin : Σ[ (i , _) ∈ Fin t ] (FinPair+ i) -> Fin (triangle-number t)
  ΣFinPair->TriFin ((k , k<t) , (fin-pair+ i j p)) =
    triangle-encode (i , j) ,
    trans-<-≤ (+₂-preserves-< j<sk)
      (trans-=-≤ (+-right (cong triangle-number p)) tsk≤T)
    where
    j<sk : j < suc k
    j<sk = suc-≤ (i , p)

    opaque
      unfolding triangle-number
      tsk≤T : (suc k + triangle-number k) ≤ triangle-number t
      tsk≤T = triangle-number-preserves-≤ k<t

  isInjective-ΣFinPair->TriFin : isInjective ΣFinPair->TriFin
  isInjective-ΣFinPair->TriFin
    {x₁@(k₁'@(k₁ , k₁<t) , fp₁@(fin-pair+ i₁ j₁ p₁))}
    {x₂@(k₂'@(k₂ , k₂<t) , fp₂@(fin-pair+ i₂ j₂ p₂))}
    fin-p =
    xp (cong proj₁ ijp) (cong proj₂ ijp)
    where
    module _ (ip : i₁ == i₂) (jp : j₁ == j₂) where
      kp : k₁ == k₂
      kp = sym p₁ >=> cong2 _+_ ip jp >=> p₂

      k'p : k₁' == k₂'
      k'p = fin-i-path kp

      fpp : PathP (\ii -> FinPair+ (Fin.i (k'p ii))) fp₁ fp₂
      fpp = FinPair+-pathp (cong Fin.i k'p) ip jp

      xp : x₁ == x₂
      xp ii = k'p ii , fpp ii

    ijp : (i₁ , j₁) == (i₂ , j₂)
    ijp = isEmbedding->isInjective (isEquiv->isEmbedding isEquiv-triangle-encode) (cong Fin.i fin-p)


  private
    T₁ : Type₀
    T₁ = Σ[ (i , _) ∈ Fin t ] (FinPair+ i)

    isFinSet-T₁ : isFinSet T₁
    isFinSet-T₁ =
      isFinSet-Σ isFinSet-Fin (\_ -> isFinSet-FinPair+)

    c₁ : ℕ
    c₁ = cardinality (T₁ , isFinSet-T₁)

    c₁-path : c₁ == finiteSum (\ ((i , _) : Fin t) -> suc i)
    c₁-path = cardinality-Σ (Fin t , isFinSet-Fin) (\ (i , _) -> FinPair+ i , isFinSet-FinPair+)


    T₂ : Type₀
    T₂ = Fin (triangle-number t)

    isFinSet-T₂ : isFinSet T₂
    isFinSet-T₂ = isFinSet-Fin

    c₂ : ℕ
    c₂ = cardinality (T₂ , isFinSet-T₂)

    c₂-path : c₂ == finiteSum (\ ((i , _) : Fin t) -> suc i)
    c₂-path = sym (triangle-number-finiteSum-path t)

    c-path : c₁ == c₂
    c-path = c₁-path >=> sym c₂-path


  isEquiv-ΣFinPair->TriFin : isEquiv ΣFinPair->TriFin
  isEquiv-ΣFinPair->TriFin =
    FinSet-isInjective->isEquiv
      (T₁ , isFinSet-T₁)
      (T₂ , isFinSet-T₂)
      c-path
      isInjective-ΣFinPair->TriFin


module _
  {ℓD : Level} {D : Type ℓD}
  {CM : CommMonoid D}
  (f : ℕ × ℕ -> D)
  (t : ℕ)
  where

  private
    T : Type₀
    T = Σ[ (k , _) ∈ Fin t ] (FinPair+ k)

    instance
      isFinSetStr-ΣFP : FinSetStr T
      isFinSetStr-ΣFP =
        record { isFin = isFinSet-Σ isFinSet-Fin (\_ -> isFinSet-FinPair+) }

    finiteMerge-triangle-encode₁ :
      finiteMerge CM (\ ((i , _) : Fin (triangle-number t)) ->
                        f (isEqInv isEquiv-triangle-encode i)) ==
      finiteMerge CM (\ ((_ , (fin-pair+ i j _)) : T) -> f (i , j))
    finiteMerge-triangle-encode₁ = step₁ >=> step₂
      where
      eq : T ≃ Fin (triangle-number t)
      eq = _ , isEquiv-ΣFinPair->TriFin t

      step₁ :
        finiteMerge CM (\ ((i , _) : Fin (triangle-number t)) ->
                          f (isEqInv isEquiv-triangle-encode i)) ==
        finiteMerge CM (\ ((_ , (fin-pair+ i j _)) : T) ->
                          f (isEqInv isEquiv-triangle-encode (triangle-encode (i , j))))
      step₁ = finiteMerge-convert eq

      step₂ :
        finiteMerge CM (\ ((_ , (fin-pair+ i j _)) : T) ->
                          f (isEqInv isEquiv-triangle-encode (triangle-encode (i , j)))) ==
        finiteMerge CM (\ ((_ , (fin-pair+ i j _)) : T) -> f (i , j))
      step₂ ii =
        finiteMerge CM (\ ((_ , (fin-pair+ i j _)) : T) ->
                          f (isEqRet isEquiv-triangle-encode (i , j) ii))

  opaque
    finiteMerge-triangle-encode₂ :
      finiteMerge CM (\ ((i , _) : Fin (triangle-number t)) ->
                        f (isEqInv isEquiv-triangle-encode i)) ==
      finiteMerge CM (\ ((k , _) : Fin t) ->
        finiteMerge CM (\ ((fin-pair+ i j _) : (FinPair+ k)) ->
          f (i , j)))
    finiteMerge-triangle-encode₂ =
      finiteMerge-triangle-encode₁ >=>
      finiteMergeᵉ-Σ _ _
