{-# OPTIONS --cubical --safe --exact-split #-}

module coequalizer.singleton where

open import base
open import isomorphism
open import cubical
open import equality-path
open import univalence

module _ {ℓ : Level} {A : Type ℓ} (P : A -> Type ℓ) (a₀ : A) where
  private
    singleton-Π-iso : Iso (∀ (x : A) -> (a₀ == x) -> P x) (P a₀)
    singleton-Π-iso = (iso f f' f∘f' f'∘f)
      where
      f : (∀ (x : A) -> (a₀ == x) -> P x) -> P a₀
      f g = g a₀ refl

      f' : P a₀ -> (∀ (x : A) -> (a₀ == x) -> P x)
      f' pa x path = transport (\i -> P (path i)) pa

      f∘f' : ∀ pa -> f (f' pa) == pa
      f∘f' pa = transportRefl pa

      f'∘f : ∀ g -> f' (f g) == g
      f'∘f g j x path =
        transp (\i -> P (path (i ∨ j))) j (g (path j) (\i -> path (i ∧ j)))

  singleton-Π-path : (∀ (x : A) -> (a₀ == x) -> P x) == P a₀
  singleton-Π-path = isoToPath singleton-Π-iso

  singleton-Π-reduce : ∀ g -> PathP (\i -> singleton-Π-path i) g (g a₀ refl)
  singleton-Π-reduce g = isoToPath-filler singleton-Π-iso g

  singleton-Π-value : PathP (\i -> singleton-Π-path i -> P a₀) (\g -> g a₀ refl) (\g -> g)
  singleton-Π-value i =
    hcomp (\k -> \{ (i = i0) -> path2 k
                  ; (i = i1) -> (\g -> g)
                  })
          (transp (\j -> singleton-Π-path (i ∨ ~ j) -> P a₀) i (\g -> g))
    where
    path1 : (transp (\j -> singleton-Π-path (~ j) -> P a₀) i0 (\g -> g)) ==
            (\g -> (transport singleton-Π-path g))
    path1 k g = transp (\j -> P a₀) k (transp (\j -> singleton-Π-path j) i0 g)

    path2 : (transp (\j -> singleton-Π-path (~ j) -> P a₀) i0 (\g -> g)) ==
            (\g -> g a₀ refl)
    path2 = path1 >=> (transport-isoToPath singleton-Π-iso)
