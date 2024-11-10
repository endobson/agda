{-# OPTIONS --cubical --safe --exact-split #-}

module functions.embedding.sum where

open import base
open import equality-path
open import equivalence
open import functions
open import functions.embedding
open import hlevel
open import sum

module _ {ℓA ℓB ℓC : Level}
         {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {f : A -> C} {g : B -> C} where
  opaque
    isEmbedding-either : isEmbedding f -> isEmbedding g -> (∀ a b -> f a != g b) ->
                         isEmbedding (either f g)
    isEmbedding-either embed-f embed-g f!=g =
      eqInv isEmbedding-eq-hasPropFibers hasPropFibers-either
      where
      hasPropFibers-f : ∀ c -> isProp (fiber f c)
      hasPropFibers-f = eqFun isEmbedding-eq-hasPropFibers embed-f
      hasPropFibers-g : ∀ c -> isProp (fiber g c)
      hasPropFibers-g = eqFun isEmbedding-eq-hasPropFibers embed-g

      hasPropFibers-either : ∀ c -> isProp (fiber (either f g) c)
      hasPropFibers-either c (inj-l a1 , p1) (inj-l a2 , p2) =
        \i -> inj-l (fst (path1 i)) , snd (path1 i)
        where
        path1 : (a1 , p1) == (a2 , p2)
        path1 = hasPropFibers-f c (a1 , p1) (a2 , p2)
      hasPropFibers-either c (inj-l a1 , p1) (inj-r b2 , p2) =
        bot-elim (f!=g a1 b2 (p1 >=> sym p2))
      hasPropFibers-either c (inj-r b1 , p1) (inj-l a2 , p2) =
        bot-elim (f!=g a2 b1 (p2 >=> sym p1))
      hasPropFibers-either c (inj-r b1 , p1) (inj-r b2 , p2) =
        \i -> inj-r (fst (path1 i)) , snd (path1 i)
        where
        path1 : (b1 , p1) == (b2 , p2)
        path1 = hasPropFibers-g c (b1 , p1) (b2 , p2)
