{-# OPTIONS --cubical --safe --exact-split #-}

module nat.monoid-homomorphism where

open import additive-group
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import funext
open import hlevel
open import monoid
open import nat
open import sigma.base
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {M : Monoid D} where
  private
    module M = Monoid M

  abstract
    Monoidʰ-ℕ-path : {f g : ℕ -> D} ->
      Monoidʰᵉ (Monoid-+ ℕ) M f -> Monoidʰᵉ (Monoid-+ ℕ) M g ->
      (f 1 == g 1) -> (f == g)
    Monoidʰ-ℕ-path {f} {g} fʰ gʰ p1 = funExt cases
      where
      cases : (n : ℕ) -> f n == g n
      cases 0 = Monoidʰ.preserves-ε fʰ >=> sym (Monoidʰ.preserves-ε gʰ)
      cases (suc n) =
        Monoidʰ.preserves-∙ fʰ 1 n >=>
        (\i -> p1 i M.∙ (cases n i)) >=>
        sym (Monoidʰ.preserves-∙ gʰ 1 n)

    private
      isProp-ΣMonoidʰ-ℕ : (d : D) -> isProp (Σ[ f ∈ (ℕ -> D) ] (Monoidʰᵉ (Monoid-+ ℕ) M f × f 1 == d))
      isProp-ΣMonoidʰ-ℕ d (f , fʰ , f1) (g , gʰ , g1) =
        ΣProp-path (isProp× isProp-Monoidʰ (M.isSet-Domain _ _))
                   (Monoidʰ-ℕ-path fʰ gʰ (f1 >=> sym g1))


    ∃!Monoidʰ-ℕ : (d : D) -> ∃![ f ∈ (ℕ -> D) ] (Monoidʰᵉ (Monoid-+ ℕ) M f × f 1 == d)
    ∃!Monoidʰ-ℕ d = (f , fʰ , f1) , isProp-ΣMonoidʰ-ℕ d _
      where
      f : ℕ -> D
      f zero = M.ε
      f (suc n) = d M.∙ f n

      f1 : f 1 == d
      f1 = M.∙-right-ε

      f∙ : (n1 n2 : ℕ) -> f (n1 + n2) == f n1 M.∙ f n2
      f∙ zero _ = sym M.∙-left-ε
      f∙ (suc n1) n2 = cong (d M.∙_) (f∙ n1 n2) >=> sym M.∙-assoc

      fʰ : Monoidʰᵉ (Monoid-+ ℕ) M f
      fʰ = record
        { preserves-ε = refl
        ; preserves-∙ = f∙
        }
