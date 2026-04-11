{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.homotopy-group where

open import base
open import equality-path
open import group
open import hlevel.base
open import nat
open import pointed.base
open import pointed.loop-space
open import truncation.set

module _ {ℓ : Level} ((A , ★A) : Type∙ ℓ) where
  loop-group : Group ℓ
  loop-group = D , record
    { monoid = record
      { _∙_ = op
      ; ε = ∣ refl ∣
      ; ∙-left-ε = left-ε _
      ; ∙-right-ε = right-ε _
      ; ∙-assoc = \{a} {b} {c} -> assoc a b c
      ; isSet-Domain = squash
      }
    ; inverse = inv
    ; ∙-left-inverse = \{m} -> left-inv m
    ; ∙-right-inverse = \{m} -> right-inv m
    }
    where
    D : Type ℓ
    D = Squash₀ (★A == ★A)
    op : D -> D -> D
    op = ∥₀-map2 _>=>_
    inv : D -> D
    inv = ∥₀-map sym

    opaque
      left-ε : ∀ m -> (op ∣ refl ∣ m == m)
      left-ε = ∥₀-elim'
        (\_ -> isProp->isSet (squash _ _))
        (\m -> cong ∣_∣ (compPath-refl-left m))
      right-ε : ∀ m -> (op m ∣ refl ∣ == m)
      right-ε = ∥₀-elim'
        (\_ -> isProp->isSet (squash _ _))
        (\m -> cong ∣_∣ (compPath-refl-right m))

      assoc : ∀ a b c -> (op (op a b) c) == (op a (op b c))
      assoc = ∥₀-elim3'
        (\a b c -> isProp->isSet (squash _ _))
        (\a b c -> cong ∣_∣ (compPath-assoc a b c))

      left-inv : ∀ m -> op (inv m) m == ∣ refl ∣
      left-inv = ∥₀-elim'
        (\_ -> isProp->isSet (squash _ _))
        (\m -> cong ∣_∣ (compPath-sym (sym m)))

      right-inv : ∀ m -> op m (inv m) == ∣ refl ∣
      right-inv = ∥₀-elim'
        (\_ -> isProp->isSet (squash _ _))
        (\m -> cong ∣_∣ (compPath-sym m))

-- Higher Homotopy Groups
πₙ : {ℓ : Level} -> Nat⁺ -> Type∙ ℓ -> Group ℓ
πₙ (suc n , _) A∙ = loop-group (Ωⁿ n A∙)

-- Fundamental Group
π₁ : {ℓ : Level} -> Type∙ ℓ -> Group ℓ
π₁ = πₙ 1⁺

πₙ-Loop-path : {ℓ : Level} (n@(n' , _) : Nat⁺) (A∙ : Type∙ ℓ) ->
                πₙ n (Ω A∙) == πₙ (suc n' , _) A∙
πₙ-Loop-path (suc n , _) A∙ i = loop-group (Ω-Ωⁿ-path {A∙ = A∙} n (~ i))
