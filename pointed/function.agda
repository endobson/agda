{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.function where

open import base
-- open import cubical
-- open import nat
open import equality-path
-- open import equality.square
open import functions
-- open import hlevel.base
-- open import equivalence
-- open import isomorphism
-- open import type-algebra
open import pointed.base
-- open import pointed.loop-space
-- open import pointed.sequence
-- open import pointed.pullback
-- open import univalence
-- open import equivalence.base


module _ {ℓA ℓB ℓC : Level}
  {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} {C∙ : Type∙ ℓC}
  (e : A∙ ->∙ B∙) (f : A∙ ->∙ C∙) (g : B∙ ->∙ C∙)
  where
  record ->∙Tri : Type (ℓ-max ℓA ℓC) where
    constructor [_]
    field
      path : f == e >∙> g

module _ {ℓA ℓB ℓC ℓD : Level}
  {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} {C∙ : Type∙ ℓC} {D∙ : Type∙ ℓD}
  (f∙@(->∙-cons f fp) : A∙ ->∙ B∙)
  (g∙@(->∙-cons g gp) : B∙ ->∙ C∙)
  (h∙@(->∙-cons h hp) : C∙ ->∙ D∙)
  where
  >∙>-assocᵉ : (f∙ >∙> g∙) >∙> h∙ == f∙ >∙> (g∙ >∙> h∙)
  >∙>-assocᵉ = \k -> ->∙-cons (h ∘ g ∘ f) (p k)
    where
    p : cong h (cong g fp >=> gp) >=> hp ==
        cong (h ∘ g) fp >=> (cong h gp >=> hp)
    p = cong (_>=> hp) (cong-trans h (cong g fp) gp) >=>
        compPath-assoc _ _ _

module _ {ℓA ℓB ℓC ℓD : Level}
  {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} {C∙ : Type∙ ℓC} {D∙ : Type∙ ℓD}
  {e₁ : A∙ ->∙ B∙} {e₂ : B∙ ->∙ C∙} {f : A∙ ->∙ D∙} {g : B∙ ->∙ D∙} {h : C∙ ->∙ D∙}
  (t₁@([ p₁ ]) : ->∙Tri e₁ f g) (t₂@([ p₂ ]) : ->∙Tri e₂ g h)
  where
  ∘->∙Tri : ->∙Tri (e₁ >∙> e₂) f h
  ∘->∙Tri = [ (p₁ >=> cong (e₁ >∙>_) p₂ >=> sym (>∙>-assocᵉ e₁ e₂ h)) ]
