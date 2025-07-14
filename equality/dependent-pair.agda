{-# OPTIONS --cubical --safe --exact-split #-}

module equality.dependent-pair where

open import base
open import cubical
open import equality-path

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : A -> Type ℓB}
         (C : ∀ a -> B a -> Type ℓC)
  where

  module inner {a₁ a₂ : A} (p : a₁ == a₂) (b₂ : B a₂)
    where

    b₁ : B a₁
    b₁ = transport (cong B (sym p)) b₂

    C' : Σ A B -> Type ℓC
    C' (a , b) = C a b

    b₁=b₂ : PathP (\i -> B (p i)) b₁ b₂
    b₁=b₂ i = transport-filler (cong B (sym p)) b₂ (~ i)

    ab-path : (a₁ , b₁) == (a₂ , b₂)
    ab-path i = p i , b₁=b₂ i

    f₁ : C a₁ b₁ -> C a₂ b₂
    f₁ = substᵉ C' ab-path

    Cp-mid : Type ℓC
    Cp-mid = transport (\i -> B (p i) -> Type ℓC) (C a₁) b₂

    Cp₁ : C a₁ b₁ == Cp-mid
    Cp₁ k = transport-filler (\i -> B (p i) -> Type ℓC) (C a₁) k
              (transport-filler (cong B (sym p)) b₂ (~ k))

    Cp₂ : Cp-mid == C a₂ b₂
    Cp₂ k = transp (\i -> B (p (k ∨ i)) -> Type ℓC) k (C (p k)) b₂

    Cp : C a₁ b₁ == C a₂ b₂
    Cp = Cp₁ >=> Cp₂

    f₂ : C a₁ b₁ -> C a₂ b₂
    f₂ = transport Cp

  f₁=f₂-refl : ∀ (a : A) (b₂ : B a) -> inner.f₁ refl b₂ == inner.f₂ refl b₂
  f₁=f₂-refl a b₂ = cong transport (sym check-Cp)
    where
    open inner (reflᵉ a) b₂

    Cp₁-path : Cp₁ == (cong (C a) b₁=b₂ >=> sym Cp₂)
    Cp₁-path = transP-sym Cp₁-lhs (symP Cp₁-rhs)
      where
      Cp₁-lhs : PathP (\i -> (C a (b₁=b₂ i)) == (Cp₂ i)) Cp₁ refl
      Cp₁-lhs i k =
        transp (\_ -> B a -> Type ℓC) (~ k ∨ i) (C a) (b₁=b₂ (k ∨ i))

      Cp₁-rhs : PathP (\i -> (C a (b₁=b₂ (i))) == (Cp₂ (i))) (cong (C a) b₁=b₂ >=> sym Cp₂) refl
      Cp₁-rhs = symP (doubleCompPath-filler _ _ _)


    check-Cp : Cp == (\i -> C a (b₁=b₂ i))
    check-Cp =
      cong (_>=> Cp₂) Cp₁-path >=>
      compPath-assoc _ _ _ >=>
      cong ((\i -> C a (b₁=b₂ i)) >=>_) (compPath-sym _) >=>
      compPath-refl-right _

  f₁=f₂ : ∀ {a₁ a₂ : A} (p : a₁ == a₂) (b₂ : B a₂) -> inner.f₁ p b₂ == inner.f₂ p b₂
  f₁=f₂ {a₁} = J (\a₂ p -> ∀ (b₂ : B a₂) -> inner.f₁ p b₂ == inner.f₂ p b₂)
                 (f₁=f₂-refl a₁)



module _ {ℓA ℓC : Level} {A : Type ℓA} {★A : A}
         (C : ∀ a -> ★A == a -> Type ℓC)
  where
  private
    B : A -> Type ℓA
    B a = ★A == a

  g₁ : ∀ a₁ a₂ -> (p : a₁ == a₂) -> (p₂ : ★A == a₂) ->
       C a₁ (transport (\i -> ★A == (p (~ i))) p₂) ->
       C a₂ p₂
  g₁ _ _ = inner.f₁ C


  g₂ : ∀ a₁ a₂ -> (p : a₁ == a₂) -> (p₂ : ★A == a₂) ->
       C a₁ (transport (\i -> ★A == (p (~ i))) p₂) ->
       C a₂ p₂
  g₂ _ _ = inner.f₂ C

  g₁=g₂ : g₁ == g₂
  g₁=g₂ i _ _ p p₂ = f₁=f₂ C p p₂ i


  check-g₁ : g₁ ==
    \a₁ a₂ p₁ p₂ ->
      transport (\k -> C (p₁ k) (transp (\i -> ★A == (p₁ (k ∨ ~ i))) k p₂))
  check-g₁ = refl
