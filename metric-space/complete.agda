{-# OPTIONS --cubical --safe --exact-split #-}

module metric-space.complete where

open import additive-group
open import additive-group.instances.real
open import base
open import metric-space
open import metric-space.continuous
open import metric-space.instances.subspace
open import net
open import order
open import order.instances.nat
open import order.instances.real
open import real
open import real.subspace
open import relation
open import sequence
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
    no-eta-equality
    field
      close : (ε : ℝ⁺) -> isEventually n (εClose ε lim)

  record isLimitS {ℓI ℓ≼ ℓS : Level} {S : Subtype D ℓS} (n : Net (Subspace S) ℓI ℓ≼) (lim : D) :
                  Type (ℓ-max* 3 ℓI ℓ≼ ℓ-one) where
    no-eta-equality
    field
      close : (ε : ℝ⁺) -> isEventually n (\ (x , _) -> (εClose ε lim x))

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


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}}
         {f : A -> B} (cont-f : isContinuous f) where

  isContinuous-preserves-isLimit :
    {ℓI ℓ≼ : Level} {n : Net A ℓI ℓ≼} {a : A} -> isLimit n a -> isLimit (Net-map f n) (f a)
  isContinuous-preserves-isLimit {ℓI} {ℓ≼} {n} {a} isLim .isLimit.close ε =
    ∥-bind handle (isContinuous.at cont-f a ε)
    where
    handle : _ -> _
    handle (δ , close) = isEventually-map n _ _ close (isLimit.close isLim δ)


module _ {ℓA ℓB ℓS : Level} {A : Type ℓA} {B : Type ℓB}
         {{MS-A : MetricSpaceStr A}}
         {{MS-B : MetricSpaceStr B}}
         {S : Subtype A ℓS}
         {f : Subspace S -> B} where

  isLimitAt->isLimit∀Net : {ℓI ℓ≼ : Level} {a : A} {b : B} ->
    isLimitAt f a b ℓI ℓ≼ ->
    (n : Net (Subspace S) ℓI ℓ≼) -> isLimitS n a -> isLimit (Net-map f n) b
  isLimitAt->isLimit∀Net {ℓI} {ℓ≼} {a} {b} limAt n isLim-a .isLimit.close ε =
    ∥-bind handle (isLimitAt.close limAt ε)
    where
    handle : _ -> _
    handle (δ , δclose) = isEventually-map n _ _ δclose (isLimitS.close isLim-a δ)
