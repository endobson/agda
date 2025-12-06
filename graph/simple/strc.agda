{-# OPTIONS --cubical --safe --exact-split #-}

module graph.simple.strc where

open import base
open import decision
open import equality-path
open import graph.simple
open import graph.simple.decidable-path
open import graph.simple.finite-walk
open import graph.simple.inductive-walk
open import graph.simple.walk-conversion
open import graph.simple.walk-to-path
open import relation.closure
open import truncation

module _ {ℓV ℓE : Level} (G : Graph ℓV ℓE)
  where
  open Graph G
  private
    STRC = SymmetricTransitiveReflexiveClosure


    STRC->FIW'-rev : ∀ {v₁} {v₂} {v₃} -> STRC E v₂ v₁ ->
      ForwardInductiveWalk G v₂ v₃ -> ForwardInductiveWalk G v₁ v₃
    STRC->FIW' : ∀ {v₁} {v₂} {v₃} -> STRC E v₁ v₂ ->
      ForwardInductiveWalk G v₂ v₃ -> ForwardInductiveWalk G v₁ v₃


    STRC->FIW'-rev (closure-rel e) w = (walk-step _ _ _ (sym-E _ _ e) w)
    STRC->FIW'-rev (closure-refl) w = w
    STRC->FIW'-rev (closure-sym w₁) w = STRC->FIW' w₁ w
    STRC->FIW'-rev (closure-trans w₁ w₂) w =
      STRC->FIW'-rev w₂ (STRC->FIW'-rev w₁ w)


    STRC->FIW' (closure-rel e) w = (walk-step _ _ _ e w)
    STRC->FIW' (closure-refl) w = w
    STRC->FIW' (closure-sym w₁) w = STRC->FIW'-rev w₁ w
    STRC->FIW' (closure-trans w₁ w₂) w =
      STRC->FIW' w₁ (STRC->FIW' w₂ w)


    STRC->FIW : ∀ {v₁} {v₂} -> STRC E v₁ v₂ -> ForwardInductiveWalk G v₁ v₂
    STRC->FIW s = STRC->FIW' s (walk-end _)

    FIW->STRC : ∀ {v₁} {v₂} -> ForwardInductiveWalk G v₁ v₂ -> STRC E v₁ v₂
    FIW->STRC (walk-end _) = closure-refl
    FIW->STRC (walk-step _ _ _ e w) = (closure-trans (closure-rel e) (FIW->STRC w))

  decide-STRC : ∀ v₁ v₂ -> Dec (∥ STRC E v₁ v₂ ∥)
  decide-STRC v₁ v₂ = dec-map (∥-map convert₁) (∥-map convert₂) dec
    where
    dec : Dec (∃[ (w , _) ∈ GPath G ] (FiniteWalk-StartsWith w v₁ ×
                                       FiniteWalk-EndsWith w v₂))
    dec = decide-∥GPath∥ v₁ v₂

    convert₁ : (Σ[ (w , _) ∈ GPath G ] (FiniteWalk-StartsWith w v₁ ×
                                    FiniteWalk-EndsWith w v₂)) ->
           STRC E v₁ v₂
    convert₁ ((w , _) , (p₁ , p₂)) =
      subst2 (STRC E) p₁ p₂
        (FIW->STRC (FiniteWalk->ForwardInductiveWalk w))

    convert₂ : STRC E v₁ v₂ ->
            (Σ[ (w , _) ∈ GPath G ] (FiniteWalk-StartsWith w v₁ ×
                                     FiniteWalk-EndsWith w v₂))
    convert₂ s = handle (FiniteWalk->FinitePath w₁)
      where
      w₀ : ForwardInductiveWalk G v₁ v₂
      w₀ = STRC->FIW s
      w₁ : FiniteWalk G
      w₁ = ForwardInductiveWalk->FiniteWalk w₀
      handle : Σ[ w₂ ∈ FiniteWalk G ] _ -> _
      handle (w₂ , (is-path , (p₁ , p₂))) =
        (w₂ , is-path) ,
        (sym p₁ >=> ForwardInductiveWalk->FiniteWalk-StartsWith w₀ ,
         sym p₂ >=> ForwardInductiveWalk->FiniteWalk-EndsWith w₀)
