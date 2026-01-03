{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit-point where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import functions
open import heyting-field.instances.rational
open import hlevel
open import nat
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import rational
open import rational.open-interval
open import real
open import real.arithmetic
open import real.arithmetic.rational
open import real.epsilon-bounded
open import real.open-interval
open import real.order
open import real.rational
open import real.sequence.limit
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import sequence
open import sigma.base
open import subset
open import truncation

record isLimitPoint' {ℓS : Level} (S : Subtype ℝ ℓS) (x : ℝ) : Type (ℓ-max ℓS ℓ-one) where
  no-eta-equality
  field
    seq : Sequence ℝ
    S-seq : (n : ℕ) -> ⟨ S (seq n) ⟩
    seq-#x : (n : ℕ) -> (seq n) # x
    isLimit-seq : isLimit seq x

isLimitPoint : {ℓS : Level} (S : Subtype ℝ ℓS) (x : ℝ) -> Type (ℓ-max ℓS ℓ-one)
isLimitPoint S x = ∥ isLimitPoint' S x ∥

isProp-isLimitPoint : {ℓS : Level} {S : Subtype ℝ ℓS} {x : ℝ} -> isProp (isLimitPoint S x)
isProp-isLimitPoint = squash

record isLimitAt
  {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) (x : ℝ) (y : ℝ) : Type (ℓ-max ℓS ℓ-one)
  where
  no-eta-equality
  field
    limit-point : isLimitPoint S x
    δε : (δ : ℚ⁺) -> ∃[ ε ∈ ℚ⁺ ]
      ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z x) -> (sz : ⟨ S z ⟩) -> εBounded ⟨ δ ⟩ (diff (f (z , sz)) y))


abstract
  isProp-isLimitAt : {ℓS : Level} {S : Subtype ℝ ℓS} {f : ∈-Subtype S -> ℝ} {x : ℝ} {y : ℝ} ->
                     isProp (isLimitAt S f x y)
  isProp-isLimitAt l1 l2 i .isLimitAt.limit-point =
    isProp-isLimitPoint (l1 .isLimitAt.limit-point) (l2 .isLimitAt.limit-point) i
  isProp-isLimitAt l1 l2 i .isLimitAt.δε =
    isPropΠ (\δ -> squash) (l1 .isLimitAt.δε) (l2 .isLimitAt.δε) i

  isProp-ΣisLimitAt : {ℓS : Level} {S : Subtype ℝ ℓS} {f : ∈-Subtype S -> ℝ} {x : ℝ} ->
                      isProp (Σ ℝ (isLimitAt S f x))
  isProp-ΣisLimitAt {S = S} {f = f} {x = x} (y1 , lim1) (y2 , lim2) = ΣProp-path isProp-isLimitAt y1=y2
    where
    module _ where
      g : (qi1 qi2 : Iℚ) -> ℝ∈Iℚ y1 qi1 -> ℝ∈Iℚ y2 qi2 -> Touching qi1 qi2
      g qi1@(Iℚ-cons l1 u1 _) qi2@(Iℚ-cons l2 u2 _) y1∈qi1 y2∈qi2 =
        handle (split-Separated qi1 qi2)
        where
        handle : (Touching qi1 qi2 ⊎ Separated qi1 qi2) -> Touching qi1 qi2
        handle (inj-l over) = over
        handle (inj-r (inj-l u1<l2)) =
          unsquash (isProp-Touching qi1 qi2)
                   (∥-bind3 handle2 (isLimitAt.δε lim1 δ/2⁺) (isLimitAt.δε lim2 δ/2⁺)
                                    (isLimitAt.limit-point lim1))
          where
          δ : ℚ
          δ = diff u1 l2
          δ/2 : ℚ
          δ/2 = δ * 1/2
          0<δ : 0# < δ
          0<δ = trans-=-< (sym +-inverse) (+₂-preserves-< u1<l2)
          0<δ/2 : 0# < δ/2
          0<δ/2 = *-preserves-0< 0<δ 0<1/2
          δ/2⁺ : ℚ⁺
          δ/2⁺ = δ/2 , 0<δ/2

          δ<d : (ℚ->ℝ δ) < diff y1 y2
          δ<d =
            subst2 _<_ (sym ℚ->ℝ-preserves-+) refl
              (+-preserves-< (L->ℝ< (proj₁ y2∈qi2))
                             (subst2 _<_ (sym ℚ->ℝ-preserves--) refl
                                     (minus-flips-< (U->ℝ< (proj₂ y1∈qi1)))))

          handle2 :
           Σ[ ε ∈ ℚ⁺ ] ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z x) -> (sz : ⟨ S z ⟩) ->
                        εBounded δ/2 (diff (f (z , sz)) y1)) ->
           Σ[ ε ∈ ℚ⁺ ] ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z x) -> (sz : ⟨ S z ⟩) ->
                        εBounded δ/2 (diff (f (z , sz)) y2)) ->
           isLimitPoint' S x ->
           ∥ Touching qi1 qi2 ∥
          handle2 ((ε1 , 0<ε1) , bound1) ((ε2 , 0<ε2) , bound2) limP =
            ∥-bind handle3 (find-small-ℝ∈Iℚ x (ε , 0<ε))
            where
            ε : ℚ
            ε = min ε1 ε2
            0<ε : 0# < ε
            0<ε = min-property ε1 ε2 0<ε1 0<ε2
            module limP = isLimitPoint' limP
            lim-seq : isLimit limP.seq x
            lim-seq = limP.isLimit-seq
            handle3 : Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ x qi × i-width qi ≤ ε) -> ∥ Touching qi1 qi2 ∥
            handle3 (qi , x∈qi , w-qi≤ε) = ∥-bind handle4 (isLimit.close limP.isLimit-seq qi x∈qi)
              where
              handle4 : ∀Largeℕ' (\m -> ℝ∈Iℚ (limP.seq m) qi) -> ∥ Touching qi1 qi2 ∥
              handle4 (n , large-n) = bot-elim (asym-< d<δ δ<d)
                where
                p = limP.seq n
                S-p = limP.S-seq n
                p∈qi = large-n n refl-≤
                pb1 = bound1 p (weaken-εBounded (trans-≤ w-qi≤ε min-≤-left)
                                                (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                             S-p
                pb2 = bound2 p (weaken-εBounded (trans-≤ w-qi≤ε min-≤-right)
                                                (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                             S-p
                pb3 : εBounded δ (diff y1 y2)
                pb3 =
                  subst2
                    εBounded
                    +-/2-path
                    diff-trans
                    (εBounded-+ _ _
                      (subst (εBounded δ/2) (sym diff-anticommute) (εBounded-- _ pb1))
                      pb2)
                d<δ : (diff y1 y2) < ℚ->ℝ δ
                d<δ = U->ℝ< (proj₂ pb3)
        handle (inj-r (inj-r u2<l1)) =
          unsquash (isProp-Touching qi1 qi2)
                   (∥-bind3 handle2 (isLimitAt.δε lim1 δ/2⁺) (isLimitAt.δε lim2 δ/2⁺)
                                    (isLimitAt.limit-point lim1))
          where
          δ = diff u2 l1
          δ/2 = δ * 1/2
          0<δ : 0# < δ
          0<δ = trans-=-< (sym +-inverse) (+₂-preserves-< u2<l1)
          0<δ/2 : 0# < δ/2
          0<δ/2 = *-preserves-0< 0<δ 0<1/2
          δ/2⁺ = δ/2 , 0<δ/2

          δ<d : (ℚ->ℝ δ) < diff y2 y1
          δ<d =
            subst2 _<_ (sym ℚ->ℝ-preserves-+) refl
              (+-preserves-< (L->ℝ< (proj₁ y1∈qi1))
                             (subst2 _<_ (sym ℚ->ℝ-preserves--) refl
                                     (minus-flips-< (U->ℝ< (proj₂ y2∈qi2)))))

          handle2 :
           Σ[ ε ∈ ℚ⁺ ] ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z x) -> (sz : ⟨ S z ⟩) ->
                        εBounded δ/2 (diff (f (z , sz)) y1)) ->
           Σ[ ε ∈ ℚ⁺ ] ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z x) -> (sz : ⟨ S z ⟩) ->
                        εBounded δ/2 (diff (f (z , sz)) y2)) ->
           isLimitPoint' S x ->
           ∥ Touching qi1 qi2 ∥
          handle2 ((ε1 , 0<ε1) , bound1) ((ε2 , 0<ε2) , bound2) limP =
            ∥-bind handle3 (find-small-ℝ∈Iℚ x (ε , 0<ε))
            where
            ε = min ε1 ε2
            0<ε = min-property ε1 ε2 0<ε1 0<ε2
            module limP = isLimitPoint' limP
            lim-seq = limP.isLimit-seq
            handle3 : Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ x qi × i-width qi ≤ ε) -> ∥ Touching qi1 qi2 ∥
            handle3 (qi , x∈qi , w-qi≤ε) = ∥-bind handle4 (isLimit.close limP.isLimit-seq qi x∈qi)
              where
              handle4 : ∀Largeℕ' (\m -> ℝ∈Iℚ (limP.seq m) qi) -> ∥ Touching qi1 qi2 ∥
              handle4 (n , large-n) = bot-elim (asym-< d<δ δ<d)
                where
                p = limP.seq n
                S-p = limP.S-seq n
                p∈qi = large-n n refl-≤
                pb1 = bound1 p (weaken-εBounded (trans-≤ w-qi≤ε min-≤-left)
                                                (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                             S-p
                pb2 = bound2 p (weaken-εBounded (trans-≤ w-qi≤ε min-≤-right)
                                                (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                             S-p
                pb3 : εBounded δ (diff y2 y1)
                pb3 =
                  subst2
                    εBounded
                    +-/2-path
                    diff-trans
                    (εBounded-+ _ _
                      (subst (εBounded δ/2) (sym diff-anticommute) (εBounded-- _ pb2))
                      pb1)
                d<δ : (diff y2 y1) < ℚ->ℝ δ
                d<δ = U->ℝ< (proj₂ pb3)

    y1=y2 : y1 == y2
    y1=y2 = touching-ℝ∈Iℚs->path y1 y2 g
