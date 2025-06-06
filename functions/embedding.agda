{-# OPTIONS --cubical --safe --exact-split #-}

module functions.embedding where

open import base
open import cubical
open import equality-path
open import equality.fundamental
open import equivalence
open import functions
open import functions.fiber
open import funext
open import hlevel
open import isomorphism
open import relation
open import sigma
open import truncation
open import type-algebra
open import univalence


private
  variable
    ℓ : Level
    A B C : Type ℓ

isProp-isEmbedding : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {f : A -> B} ->
                     isProp (isEmbedding f)
isProp-isEmbedding = isPropΠ2 (\_ _ -> isProp-isEquiv)

hasPropFibers : Pred (A -> B) _
hasPropFibers f = ∀ b -> isProp (fiber f b)

private
  inhabited-isContr-eq : (A -> isContr A) ≃ isProp A
  inhabited-isContr-eq =
    isoToEquiv (isProp->iso forward backward (isPropΠ (\_ -> isProp-isContr)) isProp-isProp)
    where
    forward : (A -> isContr A) -> isProp A
    forward f a = isContr->isProp (f a) a

    backward : isProp A -> (A -> isContr A)
    backward p a = a , p a

opaque
  ∘-isEmbedding : {f : B -> C} {g : A -> B} -> isEmbedding f -> isEmbedding g -> isEmbedding (f ∘ g)
  ∘-isEmbedding {g = g} embed-f embed-g x1 x2 =
    ∘-isEquiv (embed-f (g x1) (g x2)) (embed-g x1 x2)

∘-Embedding : B ↪ C -> A ↪ B -> A ↪ C
∘-Embedding (f , ef) (g , eg) = f ∘ g , ∘-isEmbedding ef eg


opaque
  isEmbedding-eq-hasPropFibers : {f : A -> B} -> isEmbedding f ≃ hasPropFibers f
  isEmbedding-eq-hasPropFibers {A = A} {B = B} {f = f} =
    pathToEquiv (emb==contr-fib-fa >=> switch-fibers >=> contr-prop)
    where
    f' : (a b : A) -> (a == b) -> f a == f b
    f' a b p = cong f p

    flip-path : (b1 b2 : B) -> (b1 == b2) == (b2 == b1)
    flip-path _ _ = (ua (isoToEquiv (iso sym sym (\_ -> refl) (\_ -> refl))))

    flip-Σpath : (a : A) -> (Σ[ a2 ∈ A ] (f a == f a2)) == (Σ[ a2 ∈ A ] (f a2 == f a))
    flip-Σpath a = cong (Σ A) (\i a2 -> flip-path (f a) (f a2) i)

    emb==contr-fib-fa : isEmbedding f == (∀ a -> isContr (fiber f (f a)))
    emb==contr-fib-fa i = ∀ a -> (ua (fundamental-id (f' a)) >=>
                                  cong isContr (flip-Σpath a)) i

    switch-fibers : (∀ a -> isContr (fiber f (f a))) == (∀ b -> fiber f b -> isContr (fiber f b))
    switch-fibers = switch-fibers2 >=> switch-fibers3 >=> switch-fibers4
      where
      switch-fibers2 : (∀ a -> isContr (fiber f (f a))) ==
                       (∀ a b (p : f a == b) -> isContr (fiber f (f a)))
      switch-fibers2 =
        ua (isoToEquiv (isProp->iso sf-forward sf-backward
                                   (isPropΠ (\_ -> isProp-isContr))
                                   (isPropΠ3 (\_ _ _ -> isProp-isContr))))
        where
        sf-forward : (∀ a -> isContr (fiber f (f a))) -> (∀ a b (p : f a == b) -> isContr (fiber f (f a)))
        sf-forward c a b p = c a

        sf-backward : (∀ a b (p : f a == b) -> isContr (fiber f (f a))) -> (∀ a -> isContr (fiber f (f a)))
        sf-backward c a = c a (f a) refl

      switch-fibers3 : (∀ a b (p : f a == b) -> isContr (fiber f (f a))) ==
                       (∀ a b (p : f a == b) -> isContr (fiber f b))
      switch-fibers3 i = ∀ a b (p : f a == b) -> isContr (fiber f (p i))

      switch-fibers4 : (∀ a b (p : f a == b) -> isContr (fiber f b)) ==
                       (∀ b -> fiber f b -> isContr (fiber f b))
      switch-fibers4 = ua (isoToEquiv (iso sf-forward sf-backward (\_ -> refl) (\_ -> refl)))
        where
        sf-forward : (∀ a b (p : f a == b) -> isContr (fiber f b)) ->
                     (∀ b -> fiber f b -> isContr (fiber f b))
        sf-forward c b (a , p) = c a b p
        sf-backward : (∀ b -> fiber f b -> isContr (fiber f b)) ->
                      (∀ a b (p : f a == b) -> isContr (fiber f b))
        sf-backward c a b p = c b (a , p)


    contr-prop : (∀ b -> fiber f b -> isContr (fiber f b)) ==
                 (∀ b -> isProp (fiber f b))
    contr-prop i = ∀ b -> ua (inhabited-isContr-eq {A = fiber f b}) i

isEquiv->isEmbedding : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
                       {f : A -> B} -> isEquiv f -> isEmbedding f
isEquiv->isEmbedding isEquiv-f =
  eqInv isEmbedding-eq-hasPropFibers (\b -> isContr->isProp (isEquiv.equiv-proof isEquiv-f b))

idEmbed : {ℓ : Level} -> (A : Type ℓ) -> (A ↪ A)
idEmbed A = idfun A , isEquiv->isEmbedding (snd (idEquiv A))

private
  hasPropFibers-2of3₂ : {f : B -> C} {g : A -> B} {h : A -> C} ->
                        isComposition f g h ->
                        hasPropFibers f -> hasPropFibers h -> hasPropFibers g
  hasPropFibers-2of3₂ {f = f} {g} {h} c prop-f prop-h b = prop-g
    where
    isEmbed-f : isEmbedding f
    isEmbed-f = eqInv isEmbedding-eq-hasPropFibers prop-f

    forward : fiber g b -> fiber h (f b)
    forward (a , p) = a , sym (c a) >=> cong f p
    backward : fiber h (f b) -> fiber g b
    backward (a , p) = a , isEqInv (isEmbed-f (g a) b) (c a >=> p)

    fb : ∀ x -> backward (forward x) == x
    fb (a , p) = cong (a ,_) (cong (isEqInv eq) c-path >=> isEqRet eq p)
      where
      f' : g a == b -> f (g a) == f b
      f' = cong f
      eq : isEquiv f'
      eq = (isEmbed-f (g a) b)

      c-path : (c a >=> (sym (c a) >=> cong f p)) == cong f p
      c-path =
        sym (compPath-assoc _ _ _) >=>
        cong (_>=> (cong f p)) (compPath-sym (c a)) >=>
        compPath-refl-left (cong f p)

    prop-g : isProp (fiber g b)
    prop-g = isProp-Retract forward backward fb (prop-h (f b))

opaque
  isEmbedding-2of3₂ : {f : B -> C} {g : A -> B} {h : A -> C} ->
                      isComposition f g h ->
                      isEmbedding f -> isEmbedding h -> isEmbedding g
  isEmbedding-2of3₂ c isEmbed-f isEmbed-h =
    eqInv isEmbedding-eq-hasPropFibers (hasPropFibers-2of3₂ c
      (eqFun isEmbedding-eq-hasPropFibers isEmbed-f)
      (eqFun isEmbedding-eq-hasPropFibers isEmbed-h))

  isEmbedding-2of3₃ : {f : B -> C} {g : A -> B} {h : A -> C} ->
                    isComposition f g h ->
                    isEmbedding f -> isEmbedding g -> isEmbedding h
  isEmbedding-2of3₃ c isEmbed-f isEmbed-g =
    subst isEmbedding (funExt c) (∘-isEmbedding isEmbed-f isEmbed-g)


opaque
  isEmbedding-Image-eq : {f : A -> B} -> isEmbedding f -> A ≃ Image f
  isEmbedding-Image-eq {A = A} {B = B} {f = f} embed-f =
    equiv⁻¹ (Σfibers-eq f) >eq>
    existential-eq (\b -> equiv⁻¹ (∥-Prop-eq (eqFun isEmbedding-eq-hasPropFibers embed-f b)))
