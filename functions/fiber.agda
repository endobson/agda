{-# OPTIONS --cubical --safe --exact-split #-}

module functions.fiber where

open import base
open import cubical
open import equality-path
open import equivalence

opaque
  Σfibers-eq : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (f : A -> B) -> Σ B (fiber f) ≃ A
  Σfibers-eq {A = A} {B = B} f = g , record { equiv-proof = eq }
    where
    module _ where
      g : Σ B (fiber f) -> A
      g (b , a , p) = a

    module _ (a : A) where
      ctr : fiber g a
      ctr = (f a , a , refl) , refl

      same : ∀ (f : fiber g a) -> ctr == f
      same ((b' , a' , p1) , p2) = step1 >=> step2
        where
        step1 : Path (fiber g a) ((f a , a , refl) , refl) ((f a' , a' , refl) , p2)
        step1 i = (f (p2 (~ i)) , (p2 (~ i)) , refl) , (\j -> p2 (~ i ∨ j))

        step2 : Path (fiber g a) ((f a' , a' , refl) , p2) ((b' , a' , p1) , p2)
        step2 i = (p1 i , a' , (\j -> p1 (j ∧ i))) , p2

      eq : isContr (fiber g a)
      eq = ctr , same
