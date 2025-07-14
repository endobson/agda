{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.instances.trivial where

open import base
open import equality-path
open import funext
open import group
open import hlevel.base
open import sigma.base

GroupStr-Top : GroupStr Top
GroupStr-Top = record
  { monoid = record
    { ∙-assoc = \_ -> tt
    ; ∙-left-ε = \_ -> tt
    ; ∙-right-ε = \_ -> tt
    ; isSet-Domain = \_ _ _ _ _ _ -> tt
    }
  ; ∙-left-inverse = \_ -> tt
  ; ∙-right-inverse = \_ -> tt
  }


ZeroGroup : Group ℓ-zero
ZeroGroup = Top , GroupStr-Top


initial-Groupʰ : {ℓ : Level} (G : Group ℓ) -> Groupʰ ZeroGroup G
initial-Groupʰ G = (\_ -> G.ε) , record
  { preserves-ε = refl
  ; preserves-∙ = \_ _ -> sym G.∙-left-ε
  ; preserves-inverse = \_ -> sym G.∙-left-inverse >=> G.∙-right-ε
  }
  where
  module G = Group G

∃!initial-Groupʰ : {ℓ : Level} (G : Group ℓ) -> isContr (Groupʰ ZeroGroup G)
∃!initial-Groupʰ G = initial-Groupʰ G , isProp-initial _
  where
  isProp-initial : isProp (Groupʰ ZeroGroup G)
  isProp-initial (f₁ , h₁) (f₂ , h₂) = ΣProp-path isProp-isGroupʰ (funExt fp)
    where
    module h₁ = isGroupʰ h₁
    module h₂ = isGroupʰ h₂

    fp : ∀ x -> f₁ x == f₂ x
    fp tt = h₁.preserves-ε >=> sym h₂.preserves-ε

terminal-Groupʰ : {ℓ : Level} (G : Group ℓ) -> Groupʰ G ZeroGroup
terminal-Groupʰ G = (\_ -> tt) , record
  { preserves-ε = refl
  ; preserves-∙ = \_ _ -> refl
  ; preserves-inverse = \_ -> refl
  }

∃!terminal-Groupʰ : {ℓ : Level} (G : Group ℓ) -> isContr (Groupʰ G ZeroGroup)
∃!terminal-Groupʰ G = terminal-Groupʰ G , isProp-terminal _
  where
  isProp-terminal : isProp (Groupʰ G ZeroGroup)
  isProp-terminal (f₁ , h₁) (f₂ , h₂) = ΣProp-path isProp-isGroupʰ refl

zero-Groupʰ : {ℓ₁ ℓ₂ : Level} (G₁ : Group ℓ₁) (G₂ : Group ℓ₂) -> Groupʰ G₁ G₂
zero-Groupʰ G₁ G₂ = terminal-Groupʰ G₁ >Groupʰ> initial-Groupʰ G₂


isZeroGroup : {ℓ : Level} -> Group ℓ -> Type ℓ
isZeroGroup (D , _) = isContr D


isZeroGroup->GroupIso : {ℓ : Level} -> {G : Group ℓ} ->
  isZeroGroup G -> GroupIso G ZeroGroup
isZeroGroup->GroupIso {G = G} isContr-D =
  f , record { inv = g ; rightInv = fg ; leftInv = gf }
  where
  module G = Group G

  f : Groupʰ G ZeroGroup
  f = terminal-Groupʰ G

  g : Groupʰ ZeroGroup G
  g = initial-Groupʰ G

  fg : ∀ x -> ⟨ f ⟩ (⟨ g ⟩ x) == x
  fg _ = refl
  gf : ∀ x -> ⟨ g ⟩ (⟨ f ⟩ x) == x
  gf _ = isContr->isProp isContr-D _ _
