{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.limit-point where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import functions
open import hlevel
open import nat
open import order
open import order.instances.real
open import order.instances.nat
open import ordered-semiring
open import ordered-ring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.minmax
open import rational.order
open import rational.proper-interval
open import real
open import real.rational
open import real.arithmetic.absolute-value
open import real.order
open import real.interval
open import real.arithmetic
open import real.sequence.limit
open import real.sequence.cauchy
open import real.arithmetic.rational
open import ring.implementations.real
open import sequence
open import semiring
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

private
  ℝ⁺ : Type₁
  ℝ⁺ = Σ ℝ (0# <_)

record isLimitAt 
  {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) (x : ℝ) (y : ℝ) : Type (ℓ-max ℓS ℓ-one)
  where
  no-eta-equality
  field
    limit-point : isLimitPoint S x
    -- δε : (δ : ℝ⁺) -> ∃[ ε ∈ ℝ⁺ ] 
    --   ((z : ℝ) -> absℝ (diff z x) < ⟨ ε ⟩ -> (sz : ⟨ S z ⟩) -> absℝ (diff (f (z , sz)) y) < ⟨ δ ⟩)
    δε : (δ : ℚ⁺) -> ∃[ ε ∈ ℚ⁺ ] 
      ((z : ℝ) -> εBounded ⟨ ε ⟩ (diff z x) -> (sz : ⟨ S z ⟩) -> εBounded ⟨ δ ⟩ (diff (f (z , sz)) y))


isProp-isLimitAt : {ℓS : Level} {S : Subtype ℝ ℓS} {f : ∈-Subtype S -> ℝ} {x : ℝ} {y : ℝ} -> 
                   isProp (isLimitAt S f x y)
isProp-isLimitAt l1 l2 i .isLimitAt.limit-point =
  isProp-isLimitPoint (l1 .isLimitAt.limit-point) (l2 .isLimitAt.limit-point) i
isProp-isLimitAt l1 l2 i .isLimitAt.δε =
  isPropΠ (\δ -> squash) (l1 .isLimitAt.δε) (l2 .isLimitAt.δε) i


εI : ℚ⁺ -> Iℚ
εI (ε , 0<ε) = Iℚ-cons (- ε) ε (weaken-< (trans-< (minus-flips-0< 0<ε) 0<ε))

ℝ∈Iℚ->εBounded-diff : (qi : Iℚ) -> (x y : ℝ) -> ℝ∈Iℚ x qi -> ℝ∈Iℚ y qi -> 
                      εBounded (i-width qi) (diff x y)
ℝ∈Iℚ->εBounded-diff qi@(Iℚ-cons l u l≤u) x y (l<x , x<u) (l<y , y<u) = 
  ℝ<->L _ _ L , ℝ<->U _ _ U
  where
  d = diff l u
  U : diff x y < (ℚ->ℝ (diff l u))
  U = subst (diff x y <_) 
        (sym ℚ->ℝ-preserves-+)    
        (+-preserves-< 
          (U->ℝ< y<u) 
          (subst ((- x) <_) (sym ℚ->ℝ-preserves--) (minus-flips-< (L->ℝ< l<x))))

  U2 : diff y x < (ℚ->ℝ (diff l u))
  U2 = subst (diff y x <_) 
         (sym ℚ->ℝ-preserves-+)    
         (+-preserves-< 
           (U->ℝ< x<u) 
           (subst ((- y) <_) (sym ℚ->ℝ-preserves--) (minus-flips-< (L->ℝ< l<y))))

  L : (ℚ->ℝ (- (diff l u))) < diff x y
  L = subst2 _<_ (sym ℚ->ℝ-preserves--) (sym diff-anticommute) (minus-flips-< U2)
  

weaken-εBounded : {ε1 ε2 : ℚ} -> ε1 ≤ ε2 -> (x : ℝ) -> εBounded ε1 x -> εBounded ε2 x
weaken-εBounded ε1≤ε2 x (l , u) = 
  isLowerSet≤ x _ _ -ε2≤-ε1 l ,
  isUpperSet≤ x _ _ ε1≤ε2 u 
  where
  -ε2≤-ε1 = minus-flips-≤ ε1≤ε2

εBounded-+ : {ε1 ε2 : ℚ} (x y : ℝ) -> εBounded ε1 x -> εBounded ε2 y -> εBounded (ε1 + ε2) (x + y)
εBounded-+ {ε1} {ε2} x y ε1-x ε2-y =
  subst (Real.L (x + y)) (sym minus-distrib-plus) (proj₁ both) ,
  proj₂ both
  where
  both = ℝ∈Iℚ-+ x y (curry (ℝ-bounds->Iℚ x) ε1-x) (curry (ℝ-bounds->Iℚ y) ε2-y) ε1-x ε2-y


εBounded-- : {ε : ℚ} (x : ℝ) -> εBounded ε x -> εBounded ε (- x)
εBounded-- {ε} x ε-x = l , subst (Real.U (- x)) minus-double-inverse u
  where
  b : ℝ∈Iℚ (- x) (i- (curry (ℝ-bounds->Iℚ x) ε-x))
  b = ℝ∈Iℚ-- x (curry (ℝ-bounds->Iℚ x) ε-x) ε-x
  l : Real.L (- x) (- ε)
  l = proj₁ b 
  u : Real.U (- x) (- (- ε))
  u = proj₂ b 


isProp-ΣisLimitAt : {ℓS : Level} {S : Subtype ℝ ℓS} {f : ∈-Subtype S -> ℝ} {x : ℝ} -> 
                    isProp (Σ ℝ (isLimitAt S f x))
isProp-ΣisLimitAt {S = S} {f = f} {x = x} (y1 , lim1) (y2 , lim2) = ΣProp-path isProp-isLimitAt y1=y2
  where
  g : (qi1 qi2 : Iℚ) -> ℝ∈Iℚ y1 qi1 -> ℝ∈Iℚ y2 qi2 -> Overlap qi1 qi2
  g qi1@(Iℚ-cons l1 u1 _) qi2@(Iℚ-cons l2 u2 _) y1∈qi1 y2∈qi2 =
    handle (split-Overlap qi1 qi2)
    where
    handle : (Overlap qi1 qi2 ⊎ NonOverlap qi1 qi2) -> Overlap qi1 qi2
    handle (inj-l over) = over
    handle (inj-r (inj-l u1<l2)) = 
      unsquash (isProp-Overlap qi1 qi2) 
               (∥-bind3 handle2 (isLimitAt.δε lim1 δ/2⁺) (isLimitAt.δε lim2 δ/2⁺) 
                                (isLimitAt.limit-point lim1))
      where
      δ = diff u1 l2
      δ/2 = 1/2r * δ
      0<δ : 0# < δ
      0<δ = trans-=-< (sym +-inverse) (+₂-preserves-< u1<l2)
      0<δ/2 : 0# < δ/2
      0<δ/2 = *-preserves-0< Pos-1/2r 0<δ
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
       ∥ Overlap qi1 qi2 ∥
      handle2 ((ε1 , 0<ε1) , bound1) ((ε2 , 0<ε2) , bound2) limP = 
        ∥-bind handle3 (find-small-ℝ∈Iℚ x (ε , 0<ε))
        where
        ε = minℚ ε1 ε2
        0<ε = minℚ-property ε1 ε2 0<ε1 0<ε2
        module limP = isLimitPoint' limP
        lim-seq = limP.isLimit-seq 
        handle3 : Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ x qi × i-width qi ≤ ε) -> ∥ Overlap qi1 qi2 ∥
        handle3 (qi , x∈qi , w-qi≤ε) = ∥-bind handle4 (isLimit.close limP.isLimit-seq qi x∈qi)
          where
          handle4 : ∀Largeℕ' (\m -> ℝ∈Iℚ (limP.seq m) qi) -> ∥ Overlap qi1 qi2 ∥
          handle4 (n , large-n) = bot-elim (asym-< d<δ δ<d)
            where
            p = limP.seq n
            S-p = limP.S-seq n
            p∈qi = large-n n refl-≤
            pb1 = bound1 p (weaken-εBounded (trans-≤ w-qi≤ε (minℚ-≤-left ε1 ε2))
                                            (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                         S-p
            pb2 = bound2 p (weaken-εBounded (trans-≤ w-qi≤ε (minℚ-≤-right ε1 ε2))
                                            (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                         S-p
            pb3 : εBounded δ (diff y1 y2)
            pb3 = 
              subst2 
                εBounded 
                (1/2r-path' δ)
                diff-trans
                (εBounded-+ _ _
                  (subst (εBounded δ/2) (sym diff-anticommute) (εBounded-- _ pb1))
                  pb2)
            d<δ : (diff y1 y2) < ℚ->ℝ δ
            d<δ = U->ℝ< (proj₂ pb3)
    handle (inj-r (inj-r u2<l1)) =
      unsquash (isProp-Overlap qi1 qi2) 
               (∥-bind3 handle2 (isLimitAt.δε lim1 δ/2⁺) (isLimitAt.δε lim2 δ/2⁺) 
                                (isLimitAt.limit-point lim1))
      where
      δ = diff u2 l1
      δ/2 = 1/2r * δ
      0<δ : 0# < δ
      0<δ = trans-=-< (sym +-inverse) (+₂-preserves-< u2<l1)
      0<δ/2 : 0# < δ/2
      0<δ/2 = *-preserves-0< Pos-1/2r 0<δ
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
       ∥ Overlap qi1 qi2 ∥
      handle2 ((ε1 , 0<ε1) , bound1) ((ε2 , 0<ε2) , bound2) limP = 
        ∥-bind handle3 (find-small-ℝ∈Iℚ x (ε , 0<ε))
        where
        ε = minℚ ε1 ε2
        0<ε = minℚ-property ε1 ε2 0<ε1 0<ε2
        module limP = isLimitPoint' limP
        lim-seq = limP.isLimit-seq 
        handle3 : Σ[ qi ∈ Iℚ ] (ℝ∈Iℚ x qi × i-width qi ≤ ε) -> ∥ Overlap qi1 qi2 ∥
        handle3 (qi , x∈qi , w-qi≤ε) = ∥-bind handle4 (isLimit.close limP.isLimit-seq qi x∈qi)
          where
          handle4 : ∀Largeℕ' (\m -> ℝ∈Iℚ (limP.seq m) qi) -> ∥ Overlap qi1 qi2 ∥
          handle4 (n , large-n) = bot-elim (asym-< d<δ δ<d)
            where
            p = limP.seq n
            S-p = limP.S-seq n
            p∈qi = large-n n refl-≤
            pb1 = bound1 p (weaken-εBounded (trans-≤ w-qi≤ε (minℚ-≤-left ε1 ε2))
                                            (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                         S-p
            pb2 = bound2 p (weaken-εBounded (trans-≤ w-qi≤ε (minℚ-≤-right ε1 ε2))
                                            (diff p x) (ℝ∈Iℚ->εBounded-diff qi p x p∈qi x∈qi))
                         S-p
            pb3 : εBounded δ (diff y2 y1)
            pb3 = 
              subst2 
                εBounded 
                (1/2r-path' δ)
                diff-trans
                (εBounded-+ _ _
                  (subst (εBounded δ/2) (sym diff-anticommute) (εBounded-- _ pb2))
                  pb1)
            d<δ : (diff y2 y1) < ℚ->ℝ δ
            d<δ = U->ℝ< (proj₂ pb3)

  y1=y2 : y1 == y2
  y1=y2 = overlapping-ℝ∈Iℚs->path y1 y2 g
