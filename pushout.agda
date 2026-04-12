{-# OPTIONS --cubical --safe --exact-split #-}

module pushout where

open import base
open import cubical hiding (glue)
open import isomorphism

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} where
  data Pushout (f : A -> B) (g : A -> C) : Type (ℓ-max* 3 ℓA ℓB ℓC) where
    inj-l : B -> Pushout f g
    inj-r : C -> Pushout f g
    glue : (a : A) -> inj-l (f a) == inj-r (g a)

module _ {ℓB ℓC : Level} (B : Type ℓB) (C : Type ℓC) where
  Join : Type (ℓ-max ℓB ℓC)
  Join = Pushout {A = B × C} proj₁ proj₂

module _ {ℓA ℓB ℓC ℓR : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {R : Type ℓR}
         {f : A -> B} {g : A -> C}
         (F : B -> R) (G : C -> R) (paths : ∀ a -> F (f a) == G (g a)) where
 Pushout-rec : Pushout f g -> R
 Pushout-rec (inj-l b) = F b
 Pushout-rec (inj-r c) = G c
 Pushout-rec (glue a i) = paths a i

module _ {ℓA ℓB ℓC ℓR : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {f : A -> B} {g : A -> C}
         {R : Pushout f g -> Type ℓR}
         (F : (b : B) -> R (inj-l b)) (G : (c : C) -> R (inj-r c))
         (paths : ∀ (a : A) -> PathP (\i -> R (glue a i)) (F (f a)) (G (g a))) where
 Pushout-elim : (p : Pushout f g) -> R p
 Pushout-elim (inj-l b) = F b
 Pushout-elim (inj-r c) = G c
 Pushout-elim (glue a i) = paths a i

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> B) (g : A -> C) where
  flip-Pushout-iso : Iso (Pushout f g) (Pushout g f)
  flip-Pushout-iso = iso fwd bkw fb bf
    where
    fwd : (Pushout f g) -> (Pushout g f)
    fwd (inj-l b) = inj-r b
    fwd (inj-r c) = inj-l c
    fwd (glue a i) = glue a (~ i)

    bkw : (Pushout g f) -> (Pushout f g)
    bkw (inj-l c) = inj-r c
    bkw (inj-r b) = inj-l b
    bkw (glue a i) = glue a (~ i)

    fb : ∀ x -> fwd (bkw x) == x
    fb (inj-l _) = refl
    fb (inj-r _) = refl
    fb (glue _ _) = refl
    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l _) = refl
    bf (inj-r _) = refl
    bf (glue _ _) = refl
