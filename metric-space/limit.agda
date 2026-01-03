{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.limit where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import heyting-field.instances.real
open import hlevel
open import metric-space
open import metric-space.continuous
open import metric-space.instances.subspace
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.natural-reciprocal
open import real
open import real.subspace
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import sigma.base
open import subset
open import subset.subspace
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where

  record isAdherentPoint {ℓS : Level} (S : Subtype D ℓS) (x : D) : Type (ℓ-max* 3 ℓ-one ℓS ℓD) where
    no-eta-equality
    field
      close : ∀ (ε : ℝ⁺) -> ∃[ (y , _) ∈ Subspace S ] (εClose ε x y)


  record isAccumulationPoint {ℓS : Level} (S : Subtype D ℓS) (x : D) : Type (ℓ-max* 3 ℓ-one ℓS ℓD) where
    no-eta-equality
    field
      close : ∀ (ε : ℝ⁺) -> ∃[ (y , _) ∈ Subspace S ] (0# < distance x y × εClose ε x y)


  module _ {ℓS : Level} {S : Subtype D ℓS} {x : D} where
    opaque
      isProp-isAdherentPoint : isProp (isAdherentPoint S x)
      isProp-isAdherentPoint a1 a2 i .isAdherentPoint.close =
        isPropΠ (\_ -> squash) (a1 .isAdherentPoint.close) (a2 .isAdherentPoint.close) i

      isProp-isAccumulationPoint : isProp (isAccumulationPoint S x)
      isProp-isAccumulationPoint a1 a2 i .isAccumulationPoint.close =
        isPropΠ (\_ -> squash) (a1 .isAccumulationPoint.close) (a2 .isAccumulationPoint.close) i

      isAccumulationPoint->isAdherentPoint : isAccumulationPoint S x -> isAdherentPoint S x
      isAccumulationPoint->isAdherentPoint acc .isAdherentPoint.close ε =
        ∥-map (\(y , _ , close) -> y , close) (isAccumulationPoint.close acc ε)



module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}} where

  record isLimitAt {ℓS : Level} {S : Subtype A ℓS} (f : Subspace S -> B) (x : A) (lim : B) :
                   Type (ℓ-max* 4 ℓ-one ℓA ℓB ℓS) where
    field
      limit-point : isAdherentPoint S x
      close : ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℝ⁺ ]
        (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> εClose ε lim (f y∈))

  record isPuncturedLimitAt {ℓS : Level} {S : Subtype A ℓS} (f : Subspace S -> B) (x : A) (lim : B) :
                            Type (ℓ-max* 4 ℓ-one ℓA ℓB ℓS) where
    field
      limit-point : isAccumulationPoint S x
      close : ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℝ⁺ ]
        (∀ (y∈@(y , _) : Subspace S) -> 0# < distance x y -> εClose δ x y -> εClose ε lim (f y∈))

  module _ {ℓS : Level} {S : Subtype A ℓS} {f : Subspace S -> B} {x : A} {lim : B} where
    opaque
      isProp-isLimitAt : isProp (isLimitAt f x lim)
      isProp-isLimitAt l1 l2 i .isLimitAt.limit-point =
        isProp-isAdherentPoint (l1 .isLimitAt.limit-point) (l2 .isLimitAt.limit-point) i
      isProp-isLimitAt l1 l2 i .isLimitAt.close =
        isPropΠ (\_ -> squash) (l1 .isLimitAt.close) (l2 .isLimitAt.close) i

  module _ {ℓS : Level} {S : Subtype A ℓS} {f : Subspace S -> B} {x : A} where
    opaque
      isProp-ΣisLimitAt : isProp (Σ B (isLimitAt f x))
      isProp-ΣisLimitAt (l1 , isLim1) (l2 , isLim2) =
        ΣProp-path isProp-isLimitAt (zero-distance->path (tight-# ¬d#0))
        where
        ¬d#0 : ¬ (distance l1 l2 # 0#)
        ¬d#0 (inj-l d<0) = 0≤distanceᵉ l1 l2 d<0
        ¬d#0 (inj-r 0<d) =
          unsquash isPropBot (∥-bind2 handle (isLimitAt.close isLim1 ε⁺) (isLimitAt.close isLim2 ε⁺))
          where
          ε⁺ : ℝ⁺
          ε⁺ = (distance l1 l2) * 1/2 , *-preserves-0< 0<d 0<1/2
          handle :
            Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> εClose ε⁺ l1 (f y∈)) ->
            Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> εClose ε⁺ l2 (f y∈)) ->
            ∥ Bot ∥
          handle ((δ1 , 0<δ1) , δ1-close) ((δ2 , 0<δ2) , δ2-close) =
            ∥-map handle2 (isAdherentPoint.close (isLimitAt.limit-point isLim1) (δ3 , 0<δ3))
            where
            δ3 : ℝ
            δ3 = min δ1 δ2
            0<δ3 : 0# < δ3
            0<δ3 = min-greatest-< 0<δ1 0<δ2
            δ3⁺ : ℝ⁺
            δ3⁺ = δ3 , 0<δ3
            handle2 : Σ[ (y , _) ∈ Subspace S ] (εClose δ3⁺ x y) -> Bot
            handle2 (y∈ , dxy<δ3) =
              irrefl-< (trans-≤-< (distance-triangleᵉ _ (f y∈) _)
                                  (trans-<-= (+-preserves-< lt1 lt2) +-/2-path))
              where
              lt1 : distance l1 (f y∈) < ((distance l1 l2) * 1/2)
              lt1 = δ1-close y∈ (trans-<-≤ dxy<δ3 min-≤-left)
              lt2 : distance (f y∈) l2 < ((distance l1 l2) * 1/2)
              lt2 = trans-=-< (distance-commuteᵉ (f y∈) l2)
                              (δ2-close y∈ (trans-<-≤ dxy<δ3 min-≤-right))

  module _ {ℓS : Level} {S : Subtype A ℓS} {f : Subspace S -> B} {x : A} {lim : B} where
    opaque
      isProp-isPuncturedLimitAt : isProp (isPuncturedLimitAt f x lim)
      isProp-isPuncturedLimitAt l1 l2 i .isPuncturedLimitAt.limit-point =
        isProp-isAccumulationPoint (l1 .isPuncturedLimitAt.limit-point)
                                   (l2 .isPuncturedLimitAt.limit-point) i
      isProp-isPuncturedLimitAt l1 l2 i .isPuncturedLimitAt.close =
        isPropΠ (\_ -> squash) (l1 .isPuncturedLimitAt.close)
                               (l2 .isPuncturedLimitAt.close) i

  module _ {ℓS : Level} {S : Subtype A ℓS} {f : Subspace S -> B} {x : A} where
    opaque
      isProp-ΣisPuncturedLimitAt : isProp (Σ B (isPuncturedLimitAt f x))
      isProp-ΣisPuncturedLimitAt (l1 , isLim1) (l2 , isLim2) =
        ΣProp-path isProp-isPuncturedLimitAt (zero-distance->path (tight-# ¬d#0))
        where
        ¬d#0 : ¬ (distance l1 l2 # 0#)
        ¬d#0 (inj-l d<0) = 0≤distanceᵉ l1 l2 d<0
        ¬d#0 (inj-r 0<d) =
          unsquash isPropBot (∥-bind2 handle (isPuncturedLimitAt.close isLim1 ε⁺)
                                             (isPuncturedLimitAt.close isLim2 ε⁺))
          where
          ε⁺ : ℝ⁺
          ε⁺ = (distance l1 l2 * 1/2) , *-preserves-0< 0<d 0<1/2
          handle :
            Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> 0# < distance x y ->
                           εClose δ x y -> εClose ε⁺ l1 (f y∈)) ->
            Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> 0# < distance x y ->
                           εClose δ x y -> εClose ε⁺ l2 (f y∈)) ->
            ∥ Bot ∥
          handle ((δ1 , 0<δ1) , δ1-close) ((δ2 , 0<δ2) , δ2-close) =
            ∥-map handle2 (isAccumulationPoint.close
                            (isPuncturedLimitAt.limit-point isLim1) (δ3 , 0<δ3))
            where
            δ3 : ℝ
            δ3 = min δ1 δ2
            0<δ3 : 0# < δ3
            0<δ3 = min-greatest-< 0<δ1 0<δ2
            δ3⁺ : ℝ⁺
            δ3⁺ = δ3 , 0<δ3
            handle2 : Σ[ (y , _) ∈ Subspace S ] (0# < distance x y × εClose δ3⁺ x y) -> Bot
            handle2 (y∈ , (0<dxy , dxy<δ3)) =
              irrefl-< (trans-≤-< (distance-triangleᵉ _ (f y∈) _)
                                  (trans-<-= (+-preserves-< lt1 lt2) +-/2-path))
              where
              lt1 : distance l1 (f y∈) < ((distance l1 l2) * 1/2)
              lt1 = δ1-close y∈ 0<dxy (trans-<-≤ dxy<δ3 min-≤-left)
              lt2 : distance (f y∈) l2 < ((distance l1 l2) * 1/2)
              lt2 = trans-=-< (distance-commuteᵉ (f y∈) l2)
                              (δ2-close y∈ 0<dxy (trans-<-≤ dxy<δ3 min-≤-right))

  module _ {ℓS : Level} {S : Subtype A ℓS} {f : Subspace S -> B} {x : A} {lim1 lim2 : B} where
    isLimitAt=isPuncturedLimitAt : isLimitAt f x lim1 -> isPuncturedLimitAt f x lim2 -> lim1 == lim2
    isLimitAt=isPuncturedLimitAt isLim1 isPLim2 =
      cong fst (isProp-ΣisPuncturedLimitAt (lim1 , isPLim1) (lim2 , isPLim2))
      where
      isPLim1 : isPuncturedLimitAt f x lim1
      isPLim1 .isPuncturedLimitAt.limit-point = isPuncturedLimitAt.limit-point isPLim2
      isPLim1 .isPuncturedLimitAt.close ε =
        ∥-map (\(δ , f) -> (δ , \y _ -> f y)) (isLimitAt.close isLim1 ε)




module _ {ℓA ℓB ℓS : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}}
         {S : Subtype A ℓS}
         {f : Subspace S -> B}
         {x∈@(x , _) : Subspace S}
         where
  opaque
    isContinuousAt->isLimitAt : isContinuousAt f x∈ -> isLimitAt f x (f x∈)
    isContinuousAt->isLimitAt cf .isLimitAt.limit-point .isAdherentPoint.close (ε , 0<ε) =
      ∣ x∈ , trans-=-< (path->zero-distance (reflᵉ x)) 0<ε ∣
    isContinuousAt->isLimitAt cf .isLimitAt.close = cf


module _ {ℓA ℓB ℓS : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}}
         {S : Subtype A ℓS}
         {f : Subspace S -> B}
         {x∈@(x , _) : Subspace S} {lim : B}
         where
  opaque
    isLimitAt->isContinuousAt : isLimitAt f x lim -> isContinuousAt f x∈
    isLimitAt->isContinuousAt isLim ε⁺@(ε , 0<ε) = ∥-map handle (isLimitAt.close isLim ε'⁺)
      where
      ε' : ℝ
      ε' = ε * 1/2
      0<ε' : 0# < ε'
      0<ε' = *-preserves-0< 0<ε 0<1/2
      ε'⁺ : ℝ⁺
      ε'⁺ = ε' , 0<ε'
      handle : Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y ->
                              εClose ε'⁺ lim (f y∈)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y ->
                              εClose ε⁺ (f x∈) (f y∈))
      handle (δ⁺@(δ , 0<δ) , δ-close) = δ⁺ , δ-close'
        where
        δ-close' : ∀ (y∈@(y , _) : Subspace S) -> εClose δ⁺ x y -> εClose ε⁺ (f x∈) (f y∈)
        δ-close' y∈@(y , _) dxy<δ =
          (trans-≤-< (distance-triangleᵉ _ lim _)
                     (trans-<-= (+-preserves-< lt1 lt2) +-/2-path))
          where
          lt1 : distance (f x∈) lim < ε'
          lt1 = trans-=-< (distance-commuteᵉ (f x∈) lim)
                          (δ-close x∈ (trans-=-< (path->zero-distance (reflᵉ x)) 0<δ))
          lt2 : distance lim (f y∈) < ε'
          lt2 = δ-close y∈ dxy<δ

module _ {ℓD : Level} {D : Type ℓD} {{MS-D : MetricSpaceStr D}} where
  isCrowded : {ℓS : Level} (S : Subtype D ℓS) -> Type (ℓ-max* 3 ℓS ℓD ℓ-one)
  isCrowded S = ∀ ((x , _) : Subspace S) -> isAccumulationPoint S x
