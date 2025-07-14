{-# OPTIONS --cubical --safe --exact-split #-}

module group.path where

open import group
open import base
open import equality-path
open import monoid
open import monoid.path
open import funext
open import hlevel

module _ {ℓ : Level} {D : Type ℓ} {G₁ G₂ : GroupStr D} where
  private
    module G₁ = GroupStr G₁
    module G₂ = GroupStr G₂

  GroupStr-op-path :
    (∀ d₁ d₂ -> d₁ G₁.∙ d₂ == d₁ G₂.∙ d₂) ->
    G₁ == G₂
  GroupStr-op-path op-path = \i -> record 
    { monoid = monoid-path i
    ; inverse = \x -> inv-path x i
    ; ∙-left-inverse = left-path i
    ; ∙-right-inverse = right-path i
    }
    where
    monoid-path : G₁.monoid == G₂.monoid
    monoid-path = Monoid-op-path op-path
    ε-path : G₁.ε == G₂.ε
    ε-path i = Monoid.ε (monoid-path i)

    opaque
      inv-path : ∀ x -> G₁.inverse x == G₂.inverse x
      inv-path x =
        sym G₂.∙-right-ε >=>
        cong (_ G₂.∙_) (sym G₂.∙-right-inverse) >=>
        sym G₂.∙-assoc >=>
        (\i -> (op-path (op-path (G₁.inverse x) x (~ i)) (G₂.inverse x) (~ i))) >=>
        cong (G₁._∙ _) (G₁.∙-left-inverse) >=>
        G₁.∙-left-ε
      left-path : PathP (\i -> {a : D} -> (op-path (inv-path a i) a i) == (ε-path i)) 
                  G₁.∙-left-inverse G₂.∙-left-inverse
      left-path = isProp->PathP (\i -> isPropΠⁱ (\_ -> G₁.isSet-Domain _ _))
      right-path : PathP (\i -> {a : D} -> (op-path a (inv-path a i) i) == (ε-path i)) 
                   G₁.∙-right-inverse G₂.∙-right-inverse
      right-path = isProp->PathP (\i -> isPropΠⁱ (\_ -> G₁.isSet-Domain _ _))


-- module _ {ℓ : Level} {G₁@(D₁ , GS₁)  G₂@(D₂ , GS₂) : Group ℓ} where
--   Group-op-path : (D₁ == D₂
    

