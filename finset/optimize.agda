{-# OPTIONS --cubical --safe --exact-split #-}

module finset.optimize where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finset
open import functions
open import hlevel.base
open import hlevel.sum
open import order
open import order.flipped
open import relation
open import sigma
open import sum
open import truncation
open import type-algebra

private

  module _ {ℓT ℓ< : Level} {T : Type ℓT} {T< : Rel T ℓ<}
           {PO : isPartialOrder T<} (TO : TotalOrderStr PO) where
    private
      instance
        IPO = PO
        ITO = TO

    finite-argmin'-FinT : (n : Nat) (f : (FinT n) -> T) ->
      ¬ (FinT n) ⊎ (∃[ v ∈ (FinT n) ] ∀ (v2 : FinT n) -> f v ≤ f v2)
    finite-argmin'-FinT zero f = inj-l (\())
    finite-argmin'-FinT n@(suc n') f =
      handle (finite-argmin'-FinT n' (f ∘ inj-r))
      where
      InnerAns : Type _
      InnerAns = ∥ (Σ[ v ∈ (FinT n) ] ∀ (v2 : (FinT n)) -> f v ≤ f v2) ∥
      Ans : Type _
      Ans = ¬ (FinT n) ⊎ InnerAns

      Rec : Type _
      Rec = ¬ (FinT n') ⊎
            (∃[ v ∈ (FinT n') ] ∀ (v2 : (FinT n')) -> f (inj-r v) ≤ f (inj-r v2))

      handle : Rec -> Ans
      handle (inj-l ¬R) =
        inj-r ∣ ((inj-l tt) , best) ∣
        where
        best : (v2 : (FinT n)) -> f (inj-l tt) ≤ f v2
        best (inj-l tt) = refl-≤
        best (inj-r v) = bot-elim (¬R v)
      handle (inj-r exR) = inj-r (∥-bind handle2 exR)
        where
        handle2 : _ -> InnerAns
        handle2 (v , best') = (∥-bind handle3 (connex-≤ L R))
          where
          L = f (inj-l tt)
          R = f (inj-r v)
          handle3 : (L ≤ R) ⊎ (R ≤ L) -> InnerAns
          handle3 (inj-l L≤R) = ∣ (inj-l tt) , best ∣
            where
            best : (v2 : (FinT n)) -> f (inj-l tt) ≤ f v2
            best (inj-l tt) = refl-≤
            best (inj-r v2) = trans-≤ L≤R (best' v2)
          handle3 (inj-r R≤L) = ∣ (inj-r v) , best ∣
            where
            best : (v2 : (FinT n)) -> f (inj-r v) ≤ f v2
            best (inj-l tt) = R≤L
            best (inj-r v2) = best' v2

private
  module _
    {ℓS ℓT ℓ< : Level} {T : Type ℓT} {T< : Rel T ℓ<}
    {PO : isPartialOrder T<} (TOS : TotalOrderStr PO)
    (S : FinSet ℓS) (f : ⟨ S ⟩ -> T) where

    private
      V = ⟨ S ⟩
      instance
        IPO = PO

      Ans-min : Type _
      Ans-min = ¬ V ⊎ (∃[ v ∈ V ] ∀ (v2 : V) -> f v ≤ f v2)

      isProp-Ans-min : isProp Ans-min
      isProp-Ans-min = isProp⊎ isProp¬ squash not-both
        where
        not-both : _ -> _ -> Bot
        not-both ¬v ∃v = unsquash isPropBot (∥-map (¬v ∘ fst) ∃v)

    finite-argmin' : Ans-min
    finite-argmin' = unsquash isProp-Ans-min (∥-map handle (snd S))
      where
      handle : Σ[ n ∈ Nat ] (V ≃ Fin n) -> Ans-min
      handle (n , eq1) = eqInv full-eq (finite-argmin'-FinT TOS n g)
        where
        eq2 : V ≃ FinT n
        eq2 = eq1 >eq> pathToEquiv (sym (FinT=Fin n))

        g : FinT n -> T
        g = f ∘ eqInv eq2

        sigma-eq : (Σ[ v ∈ V ] (∀ (v2 : V) -> f v ≤ f v2)) ≃
                   (Σ[ v ∈ (FinT n) ] (∀ (v2 : (FinT n)) -> g v ≤ g v2))
        sigma-eq =
          existential-eq (\v -> reindexΠ (equiv⁻¹ eq2) (\v2 -> f v ≤ f v2)) >eq>
          reindexΣ (equiv⁻¹ eq2) (\v -> ∀ (v2 : (FinT n)) -> f v ≤ g v2)

        full-eq : (¬ V ⊎ (∃[ v ∈ V ] ∀ (v2 : V) -> f v ≤ f v2)) ≃
                  (¬ (FinT n) ⊎ (∃[ v ∈ (FinT n) ] ∀ (v2 : (FinT n)) -> g v ≤ g v2))
        full-eq = ⊎-equiv (¬-eq eq2) (∥-eq sigma-eq)


module _
  {ℓS ℓT ℓ< : Level} {T : Type ℓT} {T< : Rel T ℓ<}
  {{PO : isPartialOrder T<}} {{TOS : TotalOrderStr PO}}
  (S : FinSet ℓS) (f : ⟨ S ⟩ -> T) where

  private
    V = ⟨ S ⟩

    Ans-min : Type _
    Ans-min = ¬ V ⊎ (∃[ v ∈ V ] ∀ (v2 : V) -> f v ≤ f v2)
    Ans-max : Type _
    Ans-max = ¬ V ⊎ (∃[ v ∈ V ] ∀ (v2 : V) -> f v ≥ f v2)

  abstract
    finite-argmin : Ans-min
    finite-argmin = finite-argmin' TOS S f
    finite-argmax : Ans-max
    finite-argmax = finite-argmin' (TotalOrderStr-Flipped TOS) S f
