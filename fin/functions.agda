{-# OPTIONS --cubical --safe --exact-split #-}

module fin.functions where

open import base
open import equality
open import equivalence
open import fin
open import functions
open import hlevel
open import nat
open import relation
open import sigma.base
open import sum
open import truncation

-- Finite search functions
-- More general ones availible in finset libraries.
abstract
  finite-search : {ℓ₁ ℓ₂ : Level} {n : Nat} {P : Pred (Fin n) ℓ₁} {Q : Pred (Fin n) ℓ₂}
                  -> (Universal (P ∪ Q))
                  -> (Satisfiable P) ⊎ (Universal Q)
  finite-search {n = zero}  dec = inj-r (\ i -> (bot-elim (¬fin-zero i)))
  finite-search {n = suc _} {P} {Q} dec =
    case (dec zero-fin) return _ of \where
      (inj-l p) -> inj-l (zero-fin , p)
      (inj-r q) ->
        case (finite-search (dec ∘ suc-fin))
             return _ of \ where
          (inj-l (i , p)) -> inj-l (suc-fin i , p)
          (inj-r f) -> inj-r \ where
            (zero  , lt) -> subst Q (fin-i-path refl) q
            (suc i , lt) -> subst Q (fin-i-path refl) (f (i , pred-≤ lt))

  find-counterexample : {ℓ : Level} {n : Nat} {P : Pred (Fin n) ℓ} -> Decidable P
                        -> (Satisfiable (Comp P)) ⊎ (Universal P)
  find-counterexample dec = finite-search (\x -> ⊎-swap (dec->⊎ (dec x)))

  find-example : {ℓ : Level} {n : Nat} {P : Pred (Fin n) ℓ} -> Decidable P
                 -> (Satisfiable P) ⊎ (Universal (Comp P))
  find-example dec = finite-search (\x -> dec->⊎ (dec x))

private
  choiceΣ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : A -> Type ℓ₂} {P : (a : A) -> B a -> Type ℓ₃} ->
            (∀ (a : A) -> Σ[ b ∈ B a ] (P a b)) -> Σ[ f ∈ ((a : A) -> B a) ] (∀ a -> P a (f a))
  choiceΣ ps = (\a -> fst (ps a)) , (\a -> snd (ps a))


-- Either there is an uncovered point or it has a section
module _ {n m : Nat} (f : Fin n -> Fin m) where
  private
    -- `j` is not the image of any `i`
    neverImage : Pred (Fin m) ℓ-zero
    neverImage j = ∀ i -> (f i != j)

    -- `j` is the image of some `i`
    someImage : Pred (Fin m) ℓ-zero
    someImage j = fiber f j

    cases : (Satisfiable neverImage) ⊎ (Universal someImage)
    cases = finite-search (\j -> (⊎-swap (find-example (\i -> discreteFin (f i) j))))

    finite-inverse : (Universal someImage) ->
                     Σ[ g ∈ (Fin m -> Fin n) ] (∀ j -> f (g j) == j)
    finite-inverse = choiceΣ

    convert-neverImage : Satisfiable neverImage -> ¬ (isSurjection f)
    convert-neverImage (j , g) sur = 
      unsquash isPropBot (∥-map (\{ (i , p) -> g i p }) (sur j))
      

  abstract
    find-right-inverse : (Satisfiable neverImage) ⊎ (Section f)
    find-right-inverse = ⊎-map-right finite-inverse cases

    find-section : ¬ (isSurjection f) ⊎ (Section f)
    find-section = ⊎-map convert-neverImage finite-inverse cases


