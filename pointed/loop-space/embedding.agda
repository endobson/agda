{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.loop-space.embedding where

open import base
open import functions.embedding
open import equality-path
open import equality.null-homotopic
open import equality.square
open import equivalence
open import nat
open import funext
open import hlevel
open import functions
open import isomorphism
open import cubical
open import nat.iteration
open import pointed.base
open import pointed.loop-space

module _ {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB}
         (f∙@(->∙-cons f fp)  : A∙ ->∙ B∙) where

  isEmbedding->isEquiv-Ωf : isEmbedding (app∙ f∙) -> isEquiv (app∙ (Ωf f∙))
  isEmbedding->isEquiv-Ωf emb-f = ∘-isEquiv isEquiv-base-change (emb-f _ _)
     where
     base-change : ⟨ Ω (B , f ★A) ⟩ -> ⟨ Ω B∙ ⟩
     base-change p = sym fp ∙∙ p ∙∙ fp

     rev-change : ⟨ Ω B∙ ⟩ -> ⟨ Ω (B , f ★A) ⟩
     rev-change p = fp ∙∙ p ∙∙ sym fp

     bf : ∀ x -> rev-change (base-change x) == x
     bf x =
       (\j -> ((\i -> fp (i ∧ ~ j)) ∙∙
               ((\i -> (fp (~ i ∧ ~ j))) ∙∙
                x ∙∙
                (\i -> (fp (i ∧ ~ j)))) ∙∙
               (\i -> (fp (~ i ∧ ~ j))))) ∙∙
       ∙∙-refl-sides (refl ∙∙ x ∙∙ refl) ∙∙
       ∙∙-refl-sides x

     fb : ∀ x -> base-change (rev-change x) == x
     fb x =
       (\j -> ((\i -> fp (~ i ∨ j)) ∙∙
               ((\i -> (fp (i ∨ j))) ∙∙
                x ∙∙
                (\i -> (fp (~ i ∨ j)))) ∙∙
               (\i -> (fp (i ∨ j))))) ∙∙
       ∙∙-refl-sides (refl ∙∙ x ∙∙ refl) ∙∙
       ∙∙-refl-sides x


     isEquiv-base-change : isEquiv base-change
     isEquiv-base-change = isoToIsEquiv (iso base-change rev-change fb bf)
