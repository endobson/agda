{-# OPTIONS --cubical --safe --exact-split #-}

module finite-product.arithmetic where

open import additive-group
open import base
open import commutative-monoid
open import commutative-monoid.subtype
open import equality
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.without-point
open import finite-product
open import finset
open import finset.without-point
open import hlevel
open import order
open import order.minmax
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.negated
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.negated
open import relation
open import semiring
open import without-point

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D}
         {{AG : AdditiveGroup ACM}}
         {S : Semiring ACM}
         {LO : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
         {{Max : MaxOperationStr LO }} where
  private
    instance
      IS = S
      IACM = ACM
      IAG = AG
      ILO = LO
      PO = isLinearOrder->isPartialOrder-≯ LO
      CO = CompatibleNegatedLinearOrder LO
      POA = PartiallyOrderedAdditiveStr-Negated ACM LO
      POS = PartiallyOrderedSemiringStr-Negated S LO


    CM* : CommMonoid D
    CM* = Semiring.*-CommMonoid S


  module _ {ℓI : Level} (FI : FinSet ℓI) where
    private
      I = ⟨ FI ⟩
      instance
        FS : FinSetStr I
        FS = record { isFin = snd FI }


    finiteProductᵉ-abs≯1 : {f : I -> D} ->
      (∀ i -> abs (f i) ≯ 1#) ->
      abs (finiteProduct FI f) ≯ 1#
    finiteProductᵉ-abs≯1 {f} f≯ =
      trans-=-≤ (cong abs (finiteMerge-homo-inject CommMonoidʰ-fst))
                (snd (finiteMergeᵉ CM-D' FI f'))
      where
      D' : Type (ℓ-max ℓD ℓ<)
      D' = Σ[ d ∈ D ] (abs d ≯ 1#)
      f' : (i : I) -> D'
      f' i = f i , f≯ i

      a1≤1 : abs 1# ≤ 1#
      a1≤1 = path-≤ (abs-0≤-path 0≤1)

      p : {d1 d2 : D} -> (abs d1 ≤ 1#) -> (abs d2 ≤ 1#) -> (abs (d1 * d2) ≤ 1#)
      p ad1≤1 ad2≤1 =
        trans-=-≤ abs-distrib-*
          (trans-≤ (*₁-preserves-≤ abs-0≤ ad2≤1)
            (trans-≤-= (*₂-preserves-≤ ad1≤1 0≤1) *-left-one))

      CM-D' : CommMonoid D'
      CM-D' = SubCommMonoidStr (\_ -> isProp-≤) CM* a1≤1 p

  module _ {ℓI : Level} (FI : FinSet ℓI) where
    private
      I = ⟨ FI ⟩
      instance
        FS : FinSetStr I
        FS = record { isFin = snd FI }

    finiteProductᵉ-empty-abs<1 : {f : I -> D} ->
      (∀ i -> abs (f i) < 1#) ->
      finiteProduct FI f == 1# ->
      (¬ I)
    finiteProductᵉ-empty-abs<1 {f} f< f*=1 i = p3 (f< i)
      where
      f' : (i2 : WithoutPoint I i) -> D
      f' (i , _) = f i
      f'≯ : (i2 : WithoutPoint I i) -> abs (f' i2) ≯ 1#
      f'≯ (i , _) = asym-< (f< i)

      p1 : finiteProduct FI f == f i * finiteProduct (FinSet-WithoutPoint FI i) f'
      p1 = finiteMerge-WithoutPoint _ i f

      p2 : 1# == abs (f i) * abs (finiteProduct (FinSet-WithoutPoint FI i) f')
      p2 = sym (abs-0≤-path 0≤1) >=> cong abs (sym f*=1 >=> p1) >=> abs-distrib-*

      p3 : 1# ≤ abs (f i)
      p3 = trans-=-≤ p2 (trans-≤-= (*₁-preserves-≤ abs-0≤ (finiteProductᵉ-abs≯1 _ f'≯)) *-right-one)
