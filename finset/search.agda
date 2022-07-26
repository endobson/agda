{-# OPTIONS --cubical --safe --exact-split #-}

module finset.search where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import finset
open import functions
open import hlevel
open import relation
open import sum
open import truncation
open import fin-algebra


abstract
  private
    finite-search-FinT : {ℓ₁ ℓ₂ : Level} (n : Nat) {P : Pred (FinT n) ℓ₁} {Q : Pred (FinT n) ℓ₂}
                         -> (Universal (P ∪ Q))
                         -> (Satisfiable P) ⊎ (Universal Q)
    finite-search-FinT zero dec = inj-r (\())
    finite-search-FinT (suc n) {P} {Q} dec with (dec (inj-l tt))
    ... | (inj-l p) = inj-l (inj-l tt , p)
    ... | (inj-r q) with (finite-search-FinT n (dec ∘ inj-r))
    ...             | (inj-l (e , p)) = inj-l (inj-r e , p)
    ...             | (inj-r qs) = inj-r (\{ (inj-l tt) -> q ; (inj-r i) -> qs i})

    finite-search-Fin : {ℓ₁ ℓ₂ : Level} (n : Nat) {P : Pred (Fin n) ℓ₁} {Q : Pred (Fin n) ℓ₂}
                        -> (Universal (P ∪ Q))
                        -> (Satisfiable P) ⊎ (Universal Q)
    finite-search-Fin {ℓ₁} {ℓ₂} n = 
      subst (\F -> ∀ {P : Pred F ℓ₁} {Q : Pred F ℓ₂}
                     -> (Universal (P ∪ Q))
                     -> (Satisfiable P) ⊎ (Universal Q))
            (FinT=Fin n) (finite-search-FinT n)


  finite-search : {ℓS ℓ₁ ℓ₂ : Level} (S : FinSet ℓS) {P : Pred ⟨ S ⟩ ℓ₁} {Q : Pred ⟨ S ⟩ ℓ₂}
                  -> (Universal (P ∪ Q))
                  -> (Inhabited P) ⊎ (Universal Q)
  finite-search (S , isFinSet-S) {P = P} {Q = Q} p =
    extract2 (unsquash isProp-SideSplit (∥-map extract isFinSet-S))
    where
    module _ where
      SideSplit : Type _
      SideSplit = (∃[ s ∈ S ] (Left (p s))) ⊎ (∀ (s : S) -> Right (p s))

      isProp-SideSplit : isProp SideSplit
      isProp-SideSplit = isProp⊎ squash (isPropΠ (\_ -> isProp-Right))
                                 (\l r -> unsquash isPropBot (∥-map (handle r) l))
        where
        handle : (∀ (s : S) -> Right (p s)) -> (Σ[ s ∈ S ] (Left (p s))) -> Bot
        handle r (s , l) = ¬LeftRight l (r s)


      extract : Σ[ n ∈ Nat ] (S ≃ Fin n) -> SideSplit
      extract (n , eq) = ⊎-map l-case r-case (finite-search-Fin n Universal-P'Q')
        where
        f = (eqFun eq)
        g = (eqInv eq)

        P' : Pred (Fin n) _
        P' i = Left (p (g i))

        Q' : Pred (Fin n) _
        Q' i = Right (p (g i))

        Universal-P'Q' : Universal (P' ∪ Q')
        Universal-P'Q' i = handle (p (g i)) refl
          where
          handle : (x : _) -> x == (p (g i)) -> P' i ⊎ Q' i
          handle (inj-l _) path = inj-l (subst Left path tt)
          handle (inj-r _) path = inj-r (subst Right path tt)


        l-case : Satisfiable P' -> ∃[ s ∈ S ] (Left (p s))
        l-case (i , l) = ∣ g i , l ∣

        r-case : Universal Q' -> ∀ (s : S) -> (Right (p s))
        r-case u s = subst (\s -> Right (p s)) (eqRet eq s) (u (f s))

      extract2 : SideSplit -> (Inhabited P) ⊎ (Universal Q)
      extract2 (inj-l ∃s-Left) = inj-l (∥-map (\(s , l) -> s , proj-l (p s) l) ∃s-Left)
      extract2 (inj-r ∀s-Right) = inj-r (\s -> proj-r (p s) (∀s-Right s))


  finite-search-dec : {ℓS ℓ₁ : Level} (S : FinSet ℓS) {P : Pred ⟨ S ⟩ ℓ₁} 
                      -> (Decidable P)
                      -> (Inhabited P) ⊎ (Universal (Comp P))
  finite-search-dec S {P} dec = finite-search S (\s -> split (dec s))
    where
    split : {s : ⟨ S ⟩} -> Dec (P s) ->  P s ⊎ (¬ (P s))
    split (yes p) = inj-l p
    split (no ¬p) = inj-r ¬p

  finite-search-dec' : {ℓS ℓ₁ : Level} (S : FinSet ℓS) {P : Pred ⟨ S ⟩ ℓ₁} 
                       -> (Decidable P)
                       -> (Inhabited (Comp P)) ⊎ (Universal P)
  finite-search-dec' S {P} dec = finite-search S (\s -> split (dec s))
    where
    split : {s : ⟨ S ⟩} -> Dec (P s) -> (¬ (P s)) ⊎ (P s)
    split (yes p) = inj-r p
    split (no ¬p) = inj-l ¬p
