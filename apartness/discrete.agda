{-# OPTIONS --cubical --safe --exact-split #-}

module apartness.discrete where

open import apartness
open import base
open import equality
open import functions
open import hlevel.base
open import relation
open import truncation


module _ {ℓD : Level} {D : Type ℓD} (disc : Discrete D) where
  private
    _d#_ : Rel D ℓD
    a d# b = ¬ (a == b)

    tight-d# : Tight _d#_
    tight-d# = Dec->Stable (disc _ _)

    irrefl-d# : Irreflexive _d#_
    irrefl-d# ¬refl = ¬refl refl

    sym-d# : Symmetric _d#_
    sym-d# = _∘ sym

    comparison-d# : Comparison _d#_
    comparison-d# a b c a#c = handle (disc a b) (disc b c)
      where
      handle : Dec (a == b) -> Dec (b == c) -> ∥ (a d# b) ⊎ (b d# c) ∥
      handle (no a!=b) _         = ∣ (inj-l a!=b) ∣
      handle (yes a=b) (no b!=c) = ∣ (inj-r b!=c) ∣
      handle (yes a=b) (yes b=c) = bot-elim (a#c (a=b >=> b=c))

  TightApartnessStr-Discrete : TightApartnessStr D ℓD
  TightApartnessStr-Discrete = record
    { _#_ = _d#_
    ; TightApartness-# = tight-d# , (irrefl-d# , sym-d# , comparison-d#)
    ; isProp-# = \_ _ -> isProp¬ _
    }
