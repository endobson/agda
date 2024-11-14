{-# OPTIONS --cubical --safe --exact-split #-}

module functions.embedding.sum where

open import base
open import equality-path
open import equivalence
open import functions
open import functions.embedding
open import functions.embedding.sigma
open import hlevel
open import isomorphism
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

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} where
  opaque
    isEmbedding-inj-l : isEmbedding (inj-l {A = A} {B = B})
    isEmbedding-inj-l =
      ∘-isEmbedding (isEmbedding-fst (\_ -> isProp-Left))
                    (isEquiv->isEmbedding (snd (isoToEquiv (iso inj-l' inj-l'-rev fb bf))))
      where
      inj-l' : A -> Σ (A ⊎ B) Left
      inj-l' a = inj-l a , tt

      inj-l'-rev :  Σ (A ⊎ B) Left -> A
      inj-l'-rev (inj-l a , tt) = a

      fb : ∀ a -> inj-l' (inj-l'-rev a) == a
      fb (inj-l a , _) = refl
      bf : ∀ a -> inj-l'-rev (inj-l' a) == a
      bf a = refl

    isEmbedding-inj-r : isEmbedding (inj-r {A = A} {B = B})
    isEmbedding-inj-r =
      ∘-isEmbedding (isEmbedding-fst (\_ -> isProp-Right))
                    (isEquiv->isEmbedding (snd (isoToEquiv (iso inj-r' inj-r'-rev fb bf))))
      where
      inj-r' : B -> Σ (A ⊎ B) Right
      inj-r' b = inj-r b , tt

      inj-r'-rev :  Σ (A ⊎ B) Right -> B
      inj-r'-rev (inj-r b , tt) = b

      fb : ∀ a -> inj-r' (inj-r'-rev a) == a
      fb (inj-r a , _) = refl
      bf : ∀ a -> inj-r'-rev (inj-r' a) == a
      bf a = refl
