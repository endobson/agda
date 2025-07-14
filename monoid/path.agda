{-# OPTIONS --cubical --safe --exact-split #-}

module monoid.path where

open import base
open import monoid
open import equality-path
open import hlevel.base
open import hlevel.pi

-- TODO rename to MonoidStr
-- TODO add more dependent isPropΠⁱ

module _ {ℓ : Level} {D : Type ℓ} {M₁ M₂ : Monoid D} where
  private
    module M₁ = Monoid M₁
    module M₂ = Monoid M₂

  Monoid-op-path : 
    (∀ d₁ d₂ -> d₁ M₁.∙ d₂ == d₁ M₂.∙ d₂) ->
    M₁ == M₂
  Monoid-op-path op-path = 
    \i -> record
      { ε = ε-path i
      ; _∙_ = \x y -> op-path x y i
      ; ∙-assoc = assoc-path i
      ; ∙-left-ε = left-path i
      ; ∙-right-ε = right-path i
      ; isSet-Domain = hlevel-path i
      }
    where
    opaque
      ε-path : M₁.ε == M₂.ε
      ε-path = sym M₂.∙-left-ε >=> sym (op-path _ _) >=> M₁.∙-right-ε
      assoc-path : 
        PathP (\i -> {a b c : D} -> 
                     (op-path (op-path a b i) c i) == (op-path a (op-path b c i) i))
          M₁.∙-assoc M₂.∙-assoc
      assoc-path = isProp->PathP (\i -> isPropΠⁱ3  (\_ _ _ -> M₁.isSet-Domain _ _))
      left-path : PathP (\i -> {a : D} -> (op-path (ε-path i) a i) == a) 
                  M₁.∙-left-ε M₂.∙-left-ε
      left-path = isProp->PathP (\i -> isPropΠⁱ (\_ -> M₁.isSet-Domain _ _))
      right-path : PathP (\i -> {a : D} -> (op-path a (ε-path i) i) == a) 
                   M₁.∙-right-ε M₂.∙-right-ε
      right-path = isProp->PathP (\i -> isPropΠⁱ (\_ -> M₁.isSet-Domain _ _))
      hlevel-path : M₁.isSet-Domain == M₂.isSet-Domain
      hlevel-path = isProp-isSet M₁.isSet-Domain M₂.isSet-Domain

