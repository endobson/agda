{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.eckmann-hilton where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical
open import equality-path
open import group
open import hlevel.base
open import nat
open import order
open import order.instances.nat
open import pointed.base
open import pointed.homotopy-group
open import pointed.loop-space
open import sigma.base
open import truncation.set

private
  module _ {ℓ : Level} {A∙@(A , a) : Type∙ ℓ} where
    -- The type of Squares and the identity element
    private
      S : Type ℓ
      S = ⟨ Ωⁿ 2 A∙ ⟩
      ▪ : S
      ▪ = snd (Ωⁿ 2 A∙)

    opaque
      5comp : S -> S -> S -> S -> S -> S
      5comp base east west south north x y =
        hcomp (\z -> \{ (x = i0) -> east (~ z) y
                      ; (x = i1) -> west z y
                      ; (y = i0) -> south x (~ z)
                      ; (y = i1) -> north x z
                      })
              (base x y)

      private
        -- Validate that this is proved by reflexivity
        5comp=∙∙ : ∀ (base east west : S) ->
          5comp base east west ▪ ▪ ==
          east ∙∙ base ∙∙ west
        5comp=∙∙ _ _ _ = refl

    module _ {east west south north : S} where
      opaque
        unfolding 5comp

        5comp-shift-east :
          5comp ▪ east west south north ==
          5comp east ▪ west south north
        5comp-shift-east i x y =
          hcomp (\z -> \{ (x = i0) -> east ((~ z) ∧ (~ i)) y
                        ; (x = i1) -> west z y
                        ; (y = i0) -> south x (~ z)
                        ; (y = i1) -> north x z
                        })
                (east (x ∨ (~ i)) y)

        5comp-shift-west :
          5comp ▪ east west south north ==
          5comp west east ▪ south north
        5comp-shift-west i x y =
          hcomp (\z -> \{ (x = i0) -> east (~ z) y
                        ; (x = i1) -> west (z ∨ i) y
                        ; (y = i0) -> south x (~ z)
                        ; (y = i1) -> north x z
                        })
                (west (x ∧ i) y)

        5comp-shift-south :
          5comp ▪ east west south north ==
          5comp south east west ▪ north
        5comp-shift-south i x y =
          hcomp (\z -> \{ (x = i0) -> east (~ z) y
                        ; (x = i1) -> west z y
                        ; (y = i0) -> south x ((~ z) ∧ (~ i))
                        ; (y = i1) -> north x z
                        })
                (south x (y ∨ (~ i)))

        5comp-shift-north :
          5comp ▪ east west south north ==
          5comp north east west south ▪
        5comp-shift-north i x y =
          hcomp (\z -> \{ (x = i0) -> east (~ z) y
                        ; (x = i1) -> west z y
                        ; (y = i0) -> south x (~ z)
                        ; (y = i1) -> north x (z ∨ i)
                        })
                (north x (y ∧ i))

    module _ (a b : S) where

      private
        comm' : 5comp ▪ a b ▪ ▪ == 5comp ▪ b a ▪ ▪
        comm' =
          5comp-shift-east >=>
          sym 5comp-shift-north >=>
          5comp-shift-west >=>
          sym 5comp-shift-east >=>
          5comp-shift-north >=>
          sym 5comp-shift-west

      opaque
        unfolding 5comp

        comm : a >=> b == b >=> a
        comm = comm'

module _ {ℓ : Level} (A∙@(A , a) : Type∙ ℓ) where
  private
    D : Type ℓ
    D = fst (πₙ 2⁺ A∙)
    module G = GroupStr (snd (πₙ 2⁺ A∙))

    trunc-comm : ∀ (d₁ d₂ : D) -> (d₁ G.∙ d₂) == (d₂ G.∙ d₁)
    trunc-comm =
      ∥₀-elim2'
        (\_ _ -> isProp->isSet (squash _ _))
        (\s₁ s₂ -> cong ∣_∣ (comm s₁ s₂))


  opaque
    isAbelian-π₂ : isAbelian (πₙ 2⁺ A∙)
    isAbelian-π₂ = record { ∙-commute = trunc-comm }

opaque
  isAbelian-π₂⁺ : ∀ {ℓ : Level} (n : Nat⁺) (A∙ : Type∙ ℓ) ->
                  (2 ≤ ⟨ n ⟩) -> isAbelian (πₙ n A∙)
  isAbelian-π₂⁺ n A∙ (i , p) =
    transport (\j -> isAbelian (πₙ (np j) A∙)) (isAbelian-π₂ (Ωⁿ i A∙))
    where
    np : (suc (suc i) , _) == n
    np = ΣProp-path isPropPos' (+-commuteᵉ 2 i >=> p)
