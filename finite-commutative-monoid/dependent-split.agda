{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.dependent-split where

open import base
open import commutative-monoid
open import equality
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finset.detachable
open import finset.instances.sum
open import functions
open import funext
open import hlevel
open import isomorphism
open import relation
open import subset
open import sum

module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  module _ {ℓI ℓP ℓQ : Level} {I : Type ℓI} {P : I -> Type ℓP} {Q : I -> Type ℓQ}
           {{FS-I : FinSetStr I}}
           (isContr-PQ : (i : I) -> isContr (P i ⊎ Q i)) where
    private
      isProp-P : {i : I} -> isProp (P i)
      isProp-P {i} p1 p2 =
        inj-l-injective (isContr->isProp (isContr-PQ i) (inj-l p1) (inj-l p2))
      isProp-Q : {i : I} -> isProp (Q i)
      isProp-Q {i} q1 q2 =
        inj-r-injective (isContr->isProp (isContr-PQ i) (inj-r q1) (inj-r q2))

      P' : Subtype I ℓP
      P' i = P i , isProp-P
      Q' : Subtype I ℓQ
      Q' i = Q i , isProp-Q

      Detachable-P : Detachable P'
      Detachable-P i = handle (isContr-PQ i)
        where
        handle : isContr (P i ⊎ Q i) -> Dec (P i)
        handle (inj-l p , path) = yes p
        handle (inj-r q , path) = no (\p -> inj-l!=inj-r (sym (path (inj-l p))))

      Detachable-Q : Detachable Q'
      Detachable-Q i = handle (isContr-PQ i)
        where
        handle : isContr (P i ⊎ Q i) -> Dec (Q i)
        handle (inj-l p , path) = no (\q -> inj-l!=inj-r (path (inj-r q)))
        handle (inj-r q , path) = yes q

      FS-P : FinSet (ℓ-max ℓI ℓP)
      FS-P = FinSet-Detachable (I , isFinSetⁱ) P' Detachable-P

      FS-Q : FinSet (ℓ-max ℓI ℓQ)
      FS-Q = FinSet-Detachable (I , isFinSetⁱ) Q' Detachable-Q

      split-iso : Iso (Σ I P ⊎ Σ I Q) I
      split-iso = iso forward backward fb bf
        where
        forward : (Σ I P ⊎ Σ I Q) -> I
        forward (inj-l (i , p)) = i
        forward (inj-r (i , q)) = i

        backward : I -> (Σ I P ⊎ Σ I Q)
        backward i = ⊎-map (\p -> i , p) (\q -> i , q) (fst (isContr-PQ i))

        fb : ∀ i -> forward (backward i) == i
        fb i = handle (fst (isContr-PQ i)) refl
          where
          handle : (pq : P i ⊎ Q i) -> (pq == (fst (isContr-PQ i))) -> forward (backward i) == i
          handle (inj-l p) path =
            cong forward (cong (⊎-map (\p -> i , p) (\q -> i , q)) (sym path))
          handle (inj-r q) path =
            cong forward (cong (⊎-map (\p -> i , p) (\q -> i , q)) (sym path))

        bf : ∀ pq -> backward (forward pq) == pq
        bf (inj-l (i , p)) =
          cong (⊎-map (\p -> i , p) (\q -> i , q)) (snd (isContr-PQ i) (inj-l p))
        bf (inj-r (i , q)) =
          cong (⊎-map (\p -> i , p) (\q -> i , q)) (snd (isContr-PQ i) (inj-r q))

    opaque
      finiteMerge-dependent-split : (f : I -> D) ->
        finiteMerge CM f ==
        finiteMergeᵉ CM FS-P (f ∘ fst) ∙ finiteMergeᵉ CM FS-Q (f ∘ fst)
      finiteMerge-dependent-split f =
        finiteMergeᵉ-convert-iso CM _ (FinSet-⊎ FS-P FS-Q) split-iso f >=>
        cong (finiteMergeᵉ CM _)
          (funExt (\{ (inj-l _) -> refl
                    ; (inj-r _) -> refl
                    })) >=>
        finiteMergeᵉ-⊎ CM _ _ (either (f ∘ fst) (f ∘ fst))
