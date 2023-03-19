{-# OPTIONS --cubical --safe --exact-split #-}

module int.monoid-homomorphism where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import functions
open import funext
open import int
open import monoid
open import nat
open import nat.monoid-homomorphism
open import ring.implementations.int
open import semiring
open import semiring.instances.nat
open import truncation

private
  Monoid-ℤ+ : Monoid ℤ
  Monoid-ℤ+ = CommMonoid.monoid (AdditiveCommMonoid.comm-monoid useⁱ)
  Monoid-ℕ+ : Monoid ℕ
  Monoid-ℕ+ = CommMonoid.monoid (AdditiveCommMonoid.comm-monoid useⁱ)

module _ {ℓ : Level} {D : Type ℓ} {M : Monoid D} where
  private
    module M = Monoid M

  module _ {f g : ℤ -> D} (fʰ : Monoidʰᵉ Monoid-ℤ+ M f) (gʰ : Monoidʰᵉ Monoid-ℤ+ M g)
           (p1 : f 1# == g 1#) where
    private
      ∃!ℕ->ℤ : ∃![ f ∈ (ℕ -> ℤ) ] (Monoidʰᵉ Monoid-ℕ+ Monoid-ℤ+ f × f 1# == 1#)
      ∃!ℕ->ℤ = ∃!Monoidʰ-ℕ 1#
      ℕ->ℤʰ = CommMonoidʰ.monoidʰ int-+ʰ
      f' = f ∘ ℕ->ℤ
      f'ʰ : Monoidʰᵉ Monoid-ℕ+ M (f ∘ ℕ->ℤ)
      f'ʰ = Monoidʰ-∘ fʰ ℕ->ℤʰ
      g' = g ∘ ℕ->ℤ
      g'ʰ : Monoidʰᵉ Monoid-ℕ+ M (g ∘ ℕ->ℤ)
      g'ʰ = Monoidʰ-∘ gʰ ℕ->ℤʰ

      f'==g' : f' == g'
      f'==g' = Monoidʰ-ℕ-path f'ʰ g'ʰ p1

      p-minus : ∀ n -> f (- (ℕ->ℤ n)) == g (- (ℕ->ℤ n))
      p-minus n =
        sym M.∙-right-ε >=>
        cong (f (- (ℕ->ℤ n)) M.∙_)
          (sym (Monoidʰ.preserves-ε g'ʰ) >=>
           (cong g (Monoidʰ.preserves-ε ℕ->ℤʰ >=>
                    sym +-inverse) >=>
            Monoidʰ.preserves-∙ gʰ _ _ >=>
            cong (M._∙ (g (- (ℕ->ℤ n)))) (\i -> f'==g' (~ i) n))) >=>
        sym M.∙-assoc >=>
        cong (M._∙ (g (- (ℕ->ℤ n))))
          (sym (Monoidʰ.preserves-∙ fʰ _ _) >=>
           cong f (+-commute >=> +-inverse) >=>
           Monoidʰ.preserves-ε fʰ) >=>
        M.∙-left-ε

    Monoidʰ-ℤ-path : f == g
    Monoidʰ-ℤ-path = funExt (IntElim-ℕminus'-elim (\n i -> f'==g' i n) (\n _ -> p-minus n))
