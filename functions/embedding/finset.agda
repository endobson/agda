{-# OPTIONS --cubical --safe --exact-split #-}

module functions.embedding.finset where

open import base
open import decision
open import discrete
open import equality-path
open import equivalence
open import fin
open import finset
open import finset.instances
open import finset.search
open import functions
open import functions.embedding
open import functions.embedding.fin
open import hlevel
open import sum
open import truncation

private
  module _ {ℓA ℓB : Level} (FA@(A , _) : FinSet ℓA) {B : Type ℓB} {{DB : Discrete' B}} where
    finite-search-fiber : (f : A -> B) (b : B) -> (∥ fiber f b ∥) ⊎ ¬ (fiber f b)
    finite-search-fiber f b = ⊎-map (\x -> x) convert search
      where
      search : ∥ fiber f b ∥ ⊎ (∀ a -> f a != b)
      search = finite-search-dec FA (\a -> decide-= (f a) b)

      convert : (∀ a -> f a != b) -> ¬ (fiber f b)
      convert ¬p (a , p) = ¬p a p

private
  module _ {ℓB : Level} {B : Type ℓB} {{DB : Discrete' B}} where
    private
      isSet-B : isSet B
      isSet-B = Discrete->isSet decide-=

    decide-isEmbedding-Fin : {n : Nat} -> (f : Fin n -> B) -> Dec (isEmbedding f)
    decide-isEmbedding-Fin {zero} f = yes (\ i -> bot-elim (¬fin-zero i))
    decide-isEmbedding-Fin {suc n} f = handle (decide-isEmbedding-Fin (f ∘ suc-fin))
      where
      handle : Dec (isEmbedding (f ∘ suc-fin)) -> Dec (isEmbedding f)
      handle (no ¬e) = no (\e -> ¬e (∘-isEmbedding e isEmbedding-suc-fin))
      handle (yes e) = handle2 (finite-search-fiber (_ , isFinSetⁱ) (f ∘ suc-fin) (f zero-fin))
        where
        handle2 : _ -> Dec (isEmbedding f)
        handle2 (inj-l ∣fib∣) =
          no (\e -> unsquash isPropBot
            (∥-map (\ (i , p) -> zero-fin!=suc-fin (sym (isEqInv (e _ _) p))) ∣fib∣))
        handle2 (inj-r ¬fib) =
          yes (subst isEmbedding (fin-rec-reduce f) (isEmbedding-fin-rec (isSet-B _ _) e ¬fib))

module _ {ℓA ℓB : Level} ((A , fsA) : FinSet ℓA) {B : Type ℓB} {{DB : Discrete' B}}
  where

  decide-isEmbedding : (f : A -> B) -> Dec (isEmbedding f)
  decide-isEmbedding f = unsquash (isPropDec isProp-isEmbedding) (∥-map handle fsA)
    where
    handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Dec (isEmbedding f)
    handle (n , eq) = dec-case (yes ∘ for) (\ ¬e -> no (\e -> ¬e (back e))) rec
      where
      rec : Dec (isEmbedding (f ∘ eqInv eq))
      rec = decide-isEmbedding-Fin (f ∘ eqInv eq)

      for : isEmbedding (f ∘ eqInv eq) -> isEmbedding f
      for e = subst isEmbedding (\i a -> f (eqRet eq a i)) e'
        where
        e' : isEmbedding (f ∘ eqInv eq ∘ eqFun eq)
        e' = ∘-isEmbedding e (isEquiv->isEmbedding (snd eq))
      back : isEmbedding f -> isEmbedding (f ∘ eqInv eq)
      back e = ∘-isEmbedding e (isEquiv->isEmbedding (snd (equiv⁻¹ eq)))
