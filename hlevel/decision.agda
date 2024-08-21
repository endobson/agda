{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.decision where

open import base
open import equality
open import hlevel.base
open import relation

private
  variable
    ℓ : Level
    A A₁ A₂ A₃ : Type ℓ

opaque
  -- h-level for Dec types
  isPropDec : isProp A -> isProp (Dec A)
  isPropDec ha (yes a1) (yes a2) = cong yes (ha a1 a2)
  isPropDec ha (yes a)  (no ¬a)  = bot-elim (¬a a)
  isPropDec ha (no ¬a)  (yes a)  = bot-elim (¬a a)
  isPropDec ha (no ¬a1) (no ¬a2) = cong no (isProp¬ _ ¬a1 ¬a2)

  -- h-level for Tri types
  isProp-Tri : isProp A₁ -> isProp A₂ -> isProp A₃ -> isProp (Tri A₁ A₂ A₃)
  isProp-Tri ha hb hc (tri< a1 b1 c1) (tri< a2 b2 c2) i =
    tri< (ha a1 a2 i) (isProp¬ _ b1 b2 i) (isProp¬ _ c1 c2 i)
  isProp-Tri ha hb hc (tri= a1 b1 c1) (tri= a2 b2 c2) i =
    tri= (isProp¬ _ a1 a2 i) (hb b1 b2 i) (isProp¬ _ c1 c2 i)
  isProp-Tri ha hb hc (tri> a1 b1 c1) (tri> a2 b2 c2) i =
    tri> (isProp¬ _ a1 a2 i) (isProp¬ _ b1 b2 i) (hc c1 c2 i)
  isProp-Tri ha hb hc (tri< a _ _) (tri= ¬a _ _) = bot-elim (¬a a)
  isProp-Tri ha hb hc (tri< a _ _) (tri> ¬a _ _) = bot-elim (¬a a)
  isProp-Tri ha hb hc (tri= _ b _) (tri< _ ¬b _) = bot-elim (¬b b)
  isProp-Tri ha hb hc (tri= _ b _) (tri> _ ¬b _) = bot-elim (¬b b)
  isProp-Tri ha hb hc (tri> _ _ c) (tri< _ _ ¬c) = bot-elim (¬c c)
  isProp-Tri ha hb hc (tri> _ _ c) (tri= _ _ ¬c) = bot-elim (¬c c)
