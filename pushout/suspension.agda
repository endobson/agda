{-# OPTIONS --cubical --safe --exact-split #-}

module pushout.suspension where

open import base
open import cubical hiding (glue)
open import equality-path
open import equivalence
open import isomorphism
open import pointed.suspension
open import pushout
open import pushout.3x3-lemma
open import pushout.identites

private
  ktt : {ℓ : Level} (A : Type ℓ) -> A -> Top
  ktt A _ = tt

PushoutSusp : {ℓ : Level} (A : Type ℓ)-> Type ℓ
PushoutSusp A = Pushout (ktt A) (ktt A)

module _ {ℓ : Level} (A : Type ℓ) where
  Susp-PushoutSusp-iso : Iso (Susp A) (PushoutSusp A)
  Susp-PushoutSusp-iso = iso f b fb bf
    where
    f : Susp A -> PushoutSusp A
    f north = inj-l tt
    f south = inj-r tt
    f (meridian a i) = glue a i

    b : PushoutSusp A -> Susp A
    b (inj-l tt) = north
    b (inj-r tt) = south
    b (glue a i) = meridian a i

    fb : ∀ x -> f (b x) == x
    fb (inj-l tt) = refl
    fb (inj-r tt) = refl
    fb (glue a i) = refl

    bf : ∀ x -> b (f x) == x
    bf north = refl
    bf south = refl
    bf (meridian a i) = refl


module _ {ℓ : Level} (A : Type ℓ) where
  Susp-Join-eq : (Susp A) ≃ (Join Boolean A)
  Susp-Join-eq =
    isoToEquiv (Susp-PushoutSusp-iso A) >eq>
    equiv⁻¹ r-eq >eq>
    isoToEquiv m.iso >eq>
    c-eq
    where

    -- 1    A    A
    -- 0    0    A
    -- 1    A    A

    module m = 3x3
      (ktt A) (idfun A) (idfun Bot) bot-elim (ktt A) (idfun A)
      bot-elim bot-elim bot-elim bot-elim (idfun A) (idfun A)
      (\_ -> refl) (\_ -> refl) (\_ -> refl) (\_ -> refl)

    C₀-iso : Iso m.C₀ Boolean
    C₀-iso = iso fwd bkw fb bf
      where
      fwd : m.C₀ -> Boolean
      fwd (inj-l tt) = true
      fwd (inj-r tt) = false
      bkw : Boolean -> m.C₀
      bkw true = inj-l tt
      bkw false = inj-r tt
      fb : ∀ x -> fwd (bkw x) == x
      fb true = refl
      fb false = refl
      bf : ∀ x -> bkw (fwd x) == x
      bf (inj-l tt) = refl
      bf (inj-r tt) = refl

    C₂-iso : Iso m.C₂ (Boolean × A)
    C₂-iso = iso fwd bkw fb bf
      where
      fwd : m.C₂ -> Boolean × A
      fwd (inj-l a) = true , a
      fwd (inj-r a) = false , a
      bkw : Boolean × A -> m.C₂
      bkw (true  , a) = (inj-l a)
      bkw (false , a) = (inj-r a)
      fb : ∀ x -> fwd (bkw x) == x
      fb (true  , a) = refl
      fb (false , a) = refl
      bf : ∀ x -> bkw (fwd x) == x
      bf (inj-l _) = refl
      bf (inj-r _) = refl

    C₄-iso : Iso m.C₄ A
    C₄-iso = Pushout-id-left-iso _

    c-eq : m.C ≃ (Join Boolean A)
    c-eq =
      Pushout-parts-eq _ _ (isoToEquiv C₂-iso) (isoToEquiv C₀-iso) (isoToEquiv C₄-iso) >eq>
      isoToEquiv
        (Pushout-function-iso (\{ (true , _) -> refl ; (false , _) -> refl})
                              (\{ (true , _) -> refl ; (false , _) -> refl}))

    R₀-iso : Iso m.R₀ Top
    R₀-iso = Pushout-id-right-iso _
    R₄-iso : Iso m.R₄ Top
    R₄-iso = Pushout-id-right-iso _
    R₂-iso : Iso m.R₂ A
    R₂-iso = Pushout-id-left-iso _

    r-eq : m.R ≃ PushoutSusp A
    r-eq =
      Pushout-parts-eq _ _ (isoToEquiv R₂-iso) (isoToEquiv R₀-iso) (isoToEquiv R₄-iso)
