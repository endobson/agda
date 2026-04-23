{-# OPTIONS --cubical --safe --exact-split #-}

module suspension.flattening where

open import base
open import equivalence.base
open import isomorphism
open import pointed.suspension
open import pushout
open import pushout.flattening
open import pushout.suspension
open import univalence

module _ {ℓA ℓP : Level} {A : Type ℓA} {P₁ P₂ : Type ℓP} (eq : A -> P₁ ≃ P₂)
  where
  private
    P : Susp A -> Type ℓP
    P = Susp-rec (\a -> ua (eq a))
    Q : PushoutSusp A -> Type ℓP
    Q = Pushout-rec (\_ -> P₁) (\_ -> P₂) (\a -> ua (eq a))

    f' : Σ A (\_ -> P₁) -> Σ Top (\_ -> P₁)
    f' (a , p) = (tt , p)
    g' : Σ A (\_ -> P₁) -> Σ Top (\_ -> P₂)
    g' (a , p) = (tt , eqFun (eq a) p)

    f : A × P₁ -> P₁
    f (a , p) = p
    g : A × P₁ -> P₂
    g (a , p) = eqFun (eq a) p

    step₁ : Iso (Σ (Susp A) P) (Σ (PushoutSusp A) Q)
    step₁ = iso fwd bkw fb bf
      where
      fwd : (Σ (Susp A) P) -> (Σ (PushoutSusp A) Q)
      fwd (north , p) = inj-l tt , p
      fwd (south , p) = inj-r tt , p
      fwd (meridian a i , p) = glue a i , p
      bkw : (Σ (PushoutSusp A) Q) -> (Σ (Susp A) P)
      bkw (inj-l tt , p) = north , p
      bkw (inj-r tt , p) = south , p
      bkw (glue a i , p) = meridian a i , p

      fb : ∀ x -> fwd (bkw x) == x
      fb (inj-l tt , p) = refl
      fb (inj-r tt , p) = refl
      fb (glue a i , p) = refl
      bf : ∀ x -> bkw (fwd x) == x
      bf (north , p) = refl
      bf (south , p) = refl
      bf (meridian a i , p) = refl

    step₂ : Iso (Σ (PushoutSusp A) Q) (Pushout f' g')
    step₂ = ΣPushout-iso' _ _ _ _ eq

    step₃ : Iso (Pushout f' g') (Pushout f g)
    step₃ = iso fwd bkw fb bf
      where
      fwd : Pushout f' g' -> Pushout f g
      fwd (inj-l (tt , p)) = (inj-l p)
      fwd (inj-r (tt , p)) = (inj-r p)
      fwd (glue a i) = (glue a i)
      bkw : Pushout f g -> Pushout f' g'
      bkw (inj-l p) = (inj-l (tt , p))
      bkw (inj-r p) = (inj-r (tt , p))
      bkw (glue a i) = (glue a i)

      fb : ∀ x -> fwd (bkw x) == x
      fb (inj-l _) = refl
      fb (inj-r _) = refl
      fb (glue _ _) = refl
      bf : ∀ x -> bkw (fwd x) == x
      bf (inj-l _) = refl
      bf (inj-r _) = refl
      bf (glue _ _) = refl

  ΣSusp-iso : Iso (Σ (Susp A) P) (Pushout f g)
  ΣSusp-iso = (step₁ >iso> step₂) >iso> step₃
