{-# OPTIONS --cubical --safe --exact-split #-}

module finset.search where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import finset
open import hlevel
open import relation
open import sum
open import truncation


abstract
  finite-search' : {ℓS ℓ₁ ℓ₂ : Level} (S : FinSet ℓS) {P : Pred ⟨ S ⟩ ℓ₁} {Q : Pred ⟨ S ⟩ ℓ₂}
                  -> (Universal (P ∪ Q))
                  -> (Inhabited P) ⊎ (Universal Q)
  finite-search' (S , isFinSet-S) {P = P} {Q = Q} p =
    extract2 (unsquash isProp-SideSplit (∥-map extract isFinSet-S))
    where
    SideSplit : Type _
    SideSplit = (∃[ s ∈ S ] (Left (p s))) ⊎ (∀ (s : S) -> Right (p s))

    isProp-SideSplit : isProp SideSplit
    isProp-SideSplit = isProp⊎ squash (isPropΠ (\_ -> isProp-Right))
                               (\l r -> unsquash isPropBot (∥-map (handle r) l))
      where
      handle : (∀ (s : S) -> Right (p s)) -> (Σ[ s ∈ S ] (Left (p s))) -> Bot
      handle r (s , l) = ¬LeftRight l (r s)


    extract : Σ[ n ∈ Nat ] (S ≃ Fin n) -> SideSplit
    extract (n , eq) = ⊎-map l-case r-case (finite-search Universal-P'Q')
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
