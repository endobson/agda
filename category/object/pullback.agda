{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.pullback where

open import base
open import category.base
open import equality
open import hlevel
open import truncation

module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  open CategoryHelpers C
  isPullback : {a b c : Obj C}
    (f : C [ a , c ]) (g : C [ b , c ])
    (p : Obj C) (π₁ : C [ p , a ]) (π₂ : C [ p , b ]) -> Type _
  isPullback {a} {b} f g p π₁ π₂ =
    π₁ ⋆⟨ C ⟩ f == π₂ ⋆⟨ C ⟩ g ×
    ∀ {q : Obj C} (q1 : C [ q , a ]) (q2 : C [ q , b ]) ->
      (q1 ⋆⟨ C ⟩ f == q2 ⋆⟨ C ⟩ g) ->
      ∃![ h ∈ C [ q , p ] ]
        ((h ⋆⟨ C ⟩ π₁) == q1 × ((h ⋆⟨ C ⟩ π₂) == q2))

  record Pullback {a b c : Obj C} (f : C [ a , c ]) (g : C [ b , c ]) : Type (ℓ-max ℓO ℓM) where
    field
      obj : Obj C
      π₁ : C [ obj , a ]
      π₂ : C [ obj , b ]
      is-pullback : isPullback f g obj π₁ π₂

    commutes : π₁ ⋆ f == π₂ ⋆ g
    commutes = fst is-pullback

    universal : ∀ {q} (σ₁ : C [ q , a ]) (σ₂ : C [ q , b ]) ->
      (σ₁ ⋆ f == σ₂ ⋆ g) -> ∃![ h ∈ C [ q , obj ] ] (h ⋆ π₁ == σ₁ × h ⋆ π₂ == σ₂)
    universal = snd is-pullback

  hasPullbacks : Type (ℓ-max ℓO ℓM)
  hasPullbacks = ∀ {a b c} (f : C [ a , c ]) (g : C [ b , c ]) -> Pullback f g

module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} where
  open CategoryHelpers C

  module _ {a b c : Obj C} {f : C [ a , c ]} {g : C [ b , c ]} {p1 p2 : Pullback C f g} where
    pullback-path :
      (op : Pullback.obj p1 == Pullback.obj p2) ->
      (PathP (\ i -> C [ op i , a ]) (Pullback.π₁ p1) (Pullback.π₁ p2)) ->
      (PathP (\ i -> C [ op i , b ]) (Pullback.π₂ p1) (Pullback.π₂ p2)) ->
      p1 == p2
    pullback-path op pp1 pp2 i .Pullback.obj = op i
    pullback-path op pp1 pp2 i .Pullback.π₁ = pp1 i
    pullback-path op pp1 pp2 i .Pullback.π₂ = pp2 i
    pullback-path op pp1 pp2 i .Pullback.is-pullback =
      isProp->PathPᵉ
        (\i -> isProp× (isSet-Mor C (pp1 i ⋆ f) (pp2 i ⋆ g))
                       (isPropΠⁱ (\o -> isPropΠ3 (\q1 q2 qp ->
                          isProp-isContr {A =
                            Σ[ h ∈ C [ o , op i ] ] (h ⋆ pp1 i == q1 × h ⋆ pp2 i == q2)}))))
        (Pullback.is-pullback p1) (Pullback.is-pullback p2) i
