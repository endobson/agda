{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.net-limit where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import heyting-field.instances.real
open import hlevel
open import metric-space
open import metric-space.instances.subspace
open import net
open import order
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.real
open import real.subspace
open import relation
open import ring.implementations.real
open import sigma.base
open import subset
open import subset.subspace
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where

  isCauchy : {ℓI ℓ≼ : Level} -> Pred (Net D ℓI ℓ≼) (ℓ-max* 3 ℓI ℓ≼ ℓ-one)
  isCauchy N =
    (ε : ℝ⁺) -> ∃[ n ∈ N.I ] ((m₁ m₂ : N.I) -> N.≼ n m₁ -> N.≼ n m₂ ->
                              εClose ε (N.f m₁) (N.f m₂))
    where
    module N = Net N

  record isLimit {ℓI ℓ≼ : Level} (n : Net D ℓI ℓ≼) (lim : D) : Type (ℓ-max* 3 ℓI ℓ≼ ℓ-one) where
    field
      close : (ε : ℝ⁺) -> isEventually n (εClose ε lim)

  record isLimitS {ℓI ℓ≼ ℓS : Level} {S : Subtype D ℓS} (n : Net (Subspace S) ℓI ℓ≼) (lim : D) :
                  Type (ℓ-max* 3 ℓI ℓ≼ ℓ-one) where
    no-eta-equality
    field
      close : (ε : ℝ⁺) -> isEventually n (\ (x , _) -> (εClose ε lim x))

  opaque
    isProp-isLimit : {ℓI ℓ≼ : Level} {n : Net D ℓI ℓ≼} {lim : D} -> isProp (isLimit n lim)
    isProp-isLimit isLim1 isLim2 i .isLimit.close =
      isProp->PathPᵉ (\_ -> isPropΠ (\_ -> squash)) (isLimit.close isLim1) (isLimit.close isLim2) i

    isProp-isLimitS : {ℓI ℓ≼ ℓS : Level} {S : Subtype D ℓS} {n : Net (Subspace S) ℓI ℓ≼} {lim : D} ->
                      isProp (isLimitS n lim)
    isProp-isLimitS isLim1 isLim2 i .isLimitS.close =
      isProp->PathPᵉ (\_ -> isPropΠ (\_ -> squash)) (isLimitS.close isLim1) (isLimitS.close isLim2) i

    isProp-ΣisLimit : {ℓI ℓ≼ : Level} {n : Net D ℓI ℓ≼} -> isProp (Σ D (isLimit n))
    isProp-ΣisLimit {n = n} (l1 , isLim1) (l2 , isLim2) =
      ΣProp-path isProp-isLimit (zero-distance->path (tight-# ¬d#0))
      where
      ¬d#0 : ¬ (distance l1 l2 # 0#)
      ¬d#0 (inj-l d<0) = 0≤distanceᵉ l1 l2 d<0
      ¬d#0 (inj-r 0<d) = unsquash isPropBot (∥-map handle eclose)
        where
        ε : ℝ⁺
        ε = _ , *-preserves-0< 0<1/2 0<d
        eclose : isEventually n (\ x -> (εClose ε l1 x × εClose ε l2 x))
        eclose = isEventually-∩ (isLimit.close isLim1 ε) (isLimit.close isLim2 ε)
        handle : isEventuallyΣ n (\ x -> (εClose ε l1 x × εClose ε l2 x)) -> Bot
        handle (i , close) = handle2 (close i (Net.refl-≼ n))
          where
          x : D
          x = Net.f n i
          handle2 : (εClose ε l1 x × εClose ε l2 x) -> Bot
          handle2 (d1<ε , d2<ε) =
            irrefl-< (trans-≤-< (distance-triangleᵉ l1 x l2)
                       (trans-<-= (+-preserves-< d1<ε (trans-=-< (distance-commuteᵉ x l2) d2<ε))
                         1/2-path))


  record isLimitPoint' {ℓS : Level} (S : Subtype D ℓS) (x : D) (ℓI ℓ≼ : Level) :
         Type (ℓ-max* 4 ℓS ℓD (ℓ-suc ℓI) (ℓ-suc ℓ≼)) where
    no-eta-equality
    field
      net : Net D ℓI ℓ≼
    module N = Net net

    field
      S-net : (i : N.I) -> ⟨ S (N.f i) ⟩
      net-#x : (i : N.I) -> 0# < distance x (N.f i)
      isLimit-net : isLimit net x

  isLimitPoint : {ℓS : Level} (S : Subtype D ℓS) (x : D) (ℓI ℓ≼ : Level) ->
                 Type (ℓ-max* 4 ℓS ℓD (ℓ-suc ℓI) (ℓ-suc ℓ≼))
  isLimitPoint S x ℓI ℓ≼ = ∥ isLimitPoint' S x ℓI ℓ≼ ∥

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}} where

  record isLimitAt {ℓS : Level} {S : Subtype A ℓS} (f : Subspace S -> B) (x : A) (lim : B)
                   (ℓI ℓ≼ : Level) :
                   Type (ℓ-max* 5 ℓA ℓB ℓS (ℓ-suc ℓI) (ℓ-suc ℓ≼)) where
    field
      limit-point : isLimitPoint S x ℓI ℓ≼
      close : ∀ (ε : ℝ⁺) -> ∃[ δ ∈ ℝ⁺ ]
        (∀ (y∈@(y , _) : Subspace S) -> εClose δ x y -> εClose ε lim (f y∈))


module _ {ℓD : Level} (D : Type ℓD) {{MS : MetricSpaceStr D}} where
  isComplete : (ℓI ℓ≼ : Level) -> Type (ℓ-max* 4 (ℓ-suc ℓI) (ℓ-suc ℓ≼) ℓ-one ℓD)
  isComplete ℓI ℓ≼ = ∀ (n : Net D ℓI ℓ≼) -> isCauchy n -> Σ D (isLimit n)

  isComplete₀ : Type (ℓ-max ℓ-one ℓD)
  isComplete₀ = ∀ (n : Net D ℓ-zero ℓ-zero) -> isCauchy n -> Σ D (isLimit n)
