{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.sqrt.base where

open import additive-group
open import additive-group.instances.real
open import base
open import decision
open import equality
open import heyting-field.instances.rational
open import hlevel.base
open import hlevel.sigma
open import hlevel.sum
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.natural-reciprocal
open import ordered-semiring.squares
open import rational
open import rational.order
open import rational.squares
open import real
open import real.order
open import real.rational
open import real.subspace
open import relation hiding (U)
open import ring.implementations.rational
open import semiring
open import semiring.natural-reciprocal
open import sign
open import subset.subspace
open import truncation


module _ ((x , 0≤x) : ℝ⁰⁺) where
  private
    module x = Real x

    U : Pred ℚ ℓ-zero
    U q = (0r ≤ q) × (x.U (q * q))

    L : Pred ℚ ℓ-zero
    L q = (Neg q) ⊎ ((0r ≤ q) × (x.L (q * q)))

    abstract

      isProp-U : isPropValuedPred U
      isProp-U q = isProp× isProp-≤ (x.isProp-U (q * q))

      isProp-L : isPropValuedPred L
      isProp-L q = isProp⊎ (isProp-Neg q) (isProp× isProp-≤ (x.isProp-L (q * q)))
                   (\n (0≤q , _) -> (NonNeg->¬Neg (0≤-NonNeg q 0≤q) n))

      disjoint : Universal (Comp (L ∩ U))
      disjoint q (inj-l nq , (0≤q , _)) = (NonNeg->¬Neg (0≤-NonNeg q 0≤q) nq)
      disjoint q (inj-r (_ , lqq) , (_ , uqq)) = x.disjoint (q * q) (lqq , uqq)

      Inhabited-L : Inhabited L
      Inhabited-L = ∣ (- 1r) , (inj-l (minus-flips-0< 0<1)) ∣

      Inhabited-U : Inhabited U
      Inhabited-U = ∥-map handle x.Inhabited-U
        where
        module _ where
          handle : Σ ℚ x.U -> Σ ℚ U
          handle (q , xu-q) = handle2 (split-< q 1r)
            where
            handle2 : (q < 1r ⊎ 1r ≤ q) -> Σ ℚ U
            handle2 (inj-l q<1) = 1r , (0≤1 , x.isUpperSet-U q<1*1 xu-q)
              where
              q<1*1 = subst (q <_) (sym *-right-one) q<1
            handle2 (inj-r 1≤q) = q , (0≤q , (isUpperSet≤ x q<q*q xu-q))
              where
              0≤q = trans-≤ 0≤1 1≤q
              q<q*q = subst (_≤ (q * q)) *-right-one (*₁-preserves-≤ 0≤q 1≤q)

      isUpperSet-U : isUpperSet U
      isUpperSet-U {q} {r} q<r (0≤q , xu-qq) =
        (weaken-< 0<r , x.isUpperSet-U qq<rr xu-qq)
        where
        module _ where
          0<r = trans-≤-< 0≤q q<r
          qq<rr : (q * q) < (r * r)
          qq<rr = trans-≤-< (*₁-preserves-≤ 0≤q (weaken-< q<r)) (*₂-preserves-< q<r 0<r)

      isLowerSet-L : isLowerSet L
      isLowerSet-L q<r (inj-l r<0) = (inj-l (trans-< q<r r<0))
      isLowerSet-L {q} {r} q<r (inj-r (0≤r , xu-rr)) = handle (split-< q 0r)
        where
        module _ where
          handle : (q < 0r ⊎ 0r ≤ q) -> L q
          handle (inj-l q<0) = (inj-l q<0)
          handle (inj-r 0≤q) = (inj-r (0≤q , isLowerSet≤ x qq≤rr xu-rr))
            where
            q≤r = weaken-< q<r
            qq≤rr : (q * q) ≤ (r * r)
            qq≤rr = trans-≤ (*₁-preserves-≤ 0≤q q≤r) (*₂-preserves-≤ q≤r 0≤r)


      isLowerOpen-U : isLowerOpen U
      isLowerOpen-U q (0≤q , xu-qq) = ∥-bind handle (x.isLowerOpen-U qq xu-qq)
        where
        module _ where
          qq = (q * q)
          handle : Σ[ r ∈ ℚ ] (r < qq × x.U r) -> ∃[ r ∈ ℚ ] (r < q × U r)
          handle (r , (r<qq , xu-r)) = handle2 (split-< 0r r)
            where
            handle2 : (0r < r ⊎ r ≤ 0r) -> ∃[ r ∈ ℚ ] (r < q × U r)
            handle2 (inj-r r≤0) = bot-elim (0≤x x<0)
              where
              handle3 : Σ[ s ∈ ℚ ] (s < r × x.U s) -> x ℝ<' 0#
              handle3 (s , s<r , xu-s) = (ℝ<'-cons s xu-s (ℚ<->L (trans-<-≤ s<r r≤0)))

              x<0 : x < 0#
              x<0 = ∥-map handle3 (x.isLowerOpen-U r xu-r)
            handle2 (inj-l 0<r) = ∥-map handle3 (squares-dense-upper-square 0<r 0≤q r<qq)
              where
              handle3 : _ -> Σ[ r ∈ ℚ ] (r < q × U r)
              handle3 (s , (t , 0≤t , tt=s) , r<s , s<qq) =
                t , (squares-ordered-< (convert-≤ 0≤q) tt<qq)
                  , 0≤t , subst x.U (sym tt=s) (x.isUpperSet-U r<s xu-r)
                where
                tt<qq : (t * t) < (q * q)
                tt<qq = subst (_< (q * q)) (sym tt=s) s<qq

      isUpperOpen-L : isUpperOpen L
      isUpperOpen-L q (inj-l q<0) = ∣ 1/2 * q , q<1/2q , inj-l 1/2q<0 ∣
        where
        module _ where
          q<1/2q = subst2 _<_ *-left-one refl (*₂-flips-< 1/2<1 q<0)
          1/2q<0 = subst2 _<_ refl *-right-zero (*₁-preserves-< 0<1/2 q<0)

      isUpperOpen-L q (inj-r (0≤q , xl-qq)) = ∥-bind handle (x.isUpperOpen-L qq xl-qq)
        where
        module _ where
          qq = (q * q)
          handle : Σ[ r ∈ ℚ ] (qq < r × x.L r) -> ∃[ r ∈ ℚ ] (q < r × L r)
          handle (r , (qq<r , xl-r)) = ∥-map handle2 (squares-dense-lower-square 0≤q qq<r)
            where
            handle2 : _ -> Σ[ r ∈ ℚ ] (q < r × L r)
            handle2 (s , (t , 0≤t , tt=s) , qq<s , s<r) =
              t , (squares-ordered-< (convert-≤ 0≤t) (subst2 _<_ refl (sym tt=s) qq<s)) ,
              inj-r (0≤t , subst x.L (sym tt=s) (x.isLowerSet-L s<r xl-r))

      located : (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
      located q r q<r = handle (decide-< q 0r)
        where
        handle : Dec (q < 0r) -> ∥ L q ⊎ U r ∥
        handle (yes q<0) = ∣ inj-l (inj-l q<0) ∣
        handle (no q≮0) = ∥-map handle2 (x.located qq rr qq<rr)
          where
          module _ where
            qq = (q * q)
            rr = (r * r)

            0≤q = (convert-≮ q≮0)
            0<r = trans-≤-< 0≤q q<r
            0≤r = weaken-< 0<r

            qq<rr : qq < rr
            qq<rr = squares-ordered⁺ q≮0 q<r

            handle2 : x.L qq ⊎ x.U rr -> L q ⊎ U r
            handle2 (inj-l xl-qq) = inj-l (inj-r (0≤q , xl-qq))
            handle2 (inj-r xu-rr) = inj-r (0≤r , xu-rr)

  sqrtℝᵉ : ℝ
  sqrtℝᵉ = record
    { L = L
    ; U = U
    ; isProp-L = isProp-L
    ; isProp-U = isProp-U
    ; Inhabited-L = Inhabited-L
    ; Inhabited-U = Inhabited-U
    ; isLowerSet-L = isLowerSet-L
    ; isUpperSet-U = isUpperSet-U
    ; isUpperOpen-L = isUpperOpen-L
    ; isLowerOpen-U = isLowerOpen-U
    ; disjoint = disjoint
    ; located = located
    }

  opaque
    sqrtℝ : ℝ
    sqrtℝ = sqrtℝᵉ
