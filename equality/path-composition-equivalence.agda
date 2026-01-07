{-# OPTIONS --cubical --safe --exact-split #-}

module equality.path-composition-equivalence where

open import base
open import cubical
open import equality-path
open import equality.pathp-iso
open import equivalence
open import isomorphism

opaque
  isEquiv-symP :
      {ℓ : Level} {A : I -> Type ℓ} {a₀ : A i0} {a₁ : A i1} ->
      isEquiv (\ (p : PathP A a₀ a₁) -> symP p)
  isEquiv-symP {ℓ} {A} {a₀} {a₁} = isoToIsEquiv (iso symP symP (\_ -> refl) (\_ -> refl))


private
  module isEquiv-compPath-left
    {ℓ : Level} {A : Type ℓ} {a0 : A} {a1 : A} (p₀ : Path A a0 a1) {a2 : A}
    where
    for : a1 == a2 -> a0 == a2
    for = p₀ >=>_

    back : a0 == a2 -> a1 == a2
    back = sym p₀ >=>_

    fb : ∀ x -> for (back x) == x
    fb p = q₁ >=> q₂
      where
      p'₁ : a0 == a2
      p'₁ = p₀ ∙∙ refl ∙∙ (sym p₀ ∙∙ refl ∙∙ p)

      p'₂ : a0 == a2
      p'₂ = refl ∙∙ refl ∙∙ (refl ∙∙ refl ∙∙ p)

      q₁ : p'₁ == p'₂
      q₁ j = (\i -> p₀ (i ∧ ~ j)) ∙∙ refl ∙∙ ((\i -> p₀ (~ i ∧ ~ j)) ∙∙ refl ∙∙ p)

      q₂ : p'₂ == p
      q₂ = compPath-refl-left _ >=> compPath-refl-left _

opaque
  isEquiv-compPath-left :
    {ℓ : Level} {A : Type ℓ} {a0 : A} {a1 : A} ->
    ∀ (p₀ : Path A a0 a1) (a2 : A) -> isEquiv (\ (p : a1 == a2) -> p₀ >=> p)
  isEquiv-compPath-left p₀ a2 = isoToIsEquiv (iso (for p₀) (for (sym p₀)) (fb p₀) (fb (sym p₀)))
    where
    open isEquiv-compPath-left


private
  module _ {ℓ : Level} {A : I -> Type ℓ} {a₀ : A i0} {a₁ : A i1} {a₂ : A i1} where
    Tp : (a : A i1) -> (PathP A a₀ a) == (transport (\i -> A i) a₀ == a)
    Tp _ = PathP==transport

    compPath-left'=transP-left : PathP (\i -> Tp a₁ i -> a₁ == a₂ -> Tp a₂ i)
      (\p q -> transP-left p q)
      (\p q -> refl ∙∙ p ∙∙ q)
    compPath-left'=transP-left k p q i =
      hcomp (\ j -> \ { (i = i0) -> transp (\l -> A (k ∧ l)) (~ k) a₀
                      ; (i = i1) -> q j})
            (p i)

    compPath-left=transP-left : PathP (\i -> Tp a₁ i -> a₁ == a₂ -> Tp a₂ i)
      (\p q -> transP-left p q)
      (\p q -> p >=> q)
    compPath-left=transP-left =
      transP-left compPath-left'=transP-left
        (\j p q -> (\i -> p (i ∧ j)) ∙∙ (\i -> p (j ∨ i)) ∙∙ q)

    ΣT : Type (ℓ-suc ℓ)
    ΣT = Σ[ T ∈ ((a : A i1) -> Type ℓ) ] (T a₁ -> a₁ == a₂ -> T a₂)

    isEqT : ΣT -> Type ℓ
    isEqT (T , f) = ∀ (t : T a₁) -> isEquiv (f t)

    path-ΣT :
      Path ΣT
        (PathP A a₀ , (\p q -> transP-left p q) )
        ((transport (\i -> A i) a₀ ==_) , (\p q -> p >=> q))
    path-ΣT i = ((\a -> Tp a i) , compPath-left=transP-left i)

    isEqT-lhs : isEqT (path-ΣT i1)
    isEqT-lhs p = isEquiv-compPath-left p a₂

    isEqT-rhs : isEqT (path-ΣT i0)
    isEqT-rhs = transport (\i -> isEqT (path-ΣT (~ i))) isEqT-lhs

opaque
  isEquiv-transP-left :
    {ℓ : Level} {A : I -> Type ℓ} {a₀ : A i0} {a₁ : A i1} ->
    (p₀ : PathP A a₀ a₁) (a₂ : A i1) -> isEquiv (transP-left p₀ {a₂})
  isEquiv-transP-left p₀ a₂ = isEqT-rhs p₀

  isEquiv-transP-right :
    {ℓ : Level} {A : I -> Type ℓ} {a₁ : A i0} {a₂ : A i1} ->
    (p₀ : PathP A a₁ a₂) (a₀ : A i0) -> isEquiv (\ (p : a₀ == a₁) -> transP-right p p₀)
  isEquiv-transP-right p₀ a₀ =
    ∘-isEquiv isEquiv-symP
      (∘-isEquiv (isEquiv-transP-left (symP p₀) _)
                 isEquiv-symP)
