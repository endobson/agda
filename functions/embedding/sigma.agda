{-# OPTIONS --cubical --safe --exact-split #-}

module functions.embedding.sigma where

open import base
open import equality-path
open import equality.square
open import equivalence.base
open import functions
open import functions.embedding
open import hlevel

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : (a : A) -> Type ℓB} where
  opaque
    isEmbedding-fst : (∀ a -> isProp (B a)) -> isEmbedding {A = Σ A B} fst
    isEmbedding-fst prop-b = eqInv isEmbedding-eq-hasPropFibers prop-fib
      where
      fst' : Σ A B -> A
      fst' = fst

      prop-fib : ∀ a -> isProp (fiber fst' a)
      prop-fib a ((a1 , b1) , p1) ((a2 , b2) , p2) = \i -> (p-a i , p-b i) , pp i
        where
        p-a : a1 == a2
        p-a = p1 ∙∙ refl ∙∙ (sym p2)

        pp : PathP (\i -> p-a i == a) p1 p2
        pp i j = doubleCompPath-filler p1 refl (sym p2) (~ j) i

        p-b : PathP (\i -> B (p-a i)) b1 b2
        p-b = isProp->PathP (\i -> prop-b (p-a i))


module _ {ℓA ℓB ℓC ℓD : Level}
         {A : Type ℓA} {B : A -> Type ℓB}
         {C : Type ℓC} {D : C -> Type ℓD}
         {f : A -> C}
         {g : (a : A) -> B a -> D (f a)}
  where
  private
    fg : Σ A B -> Σ C D
    fg (a , b) = f a , g a b

  opaque
    isEmbedding-Σ : isEmbedding f -> (∀ a -> isEmbedding (g a)) ->
                    isEmbedding fg
    isEmbedding-Σ embed-f embed-g = eqInv isEmbedding-eq-hasPropFibers prop-fg
      where
      prop-f : ∀ c -> isProp (fiber f c)
      prop-f = eqFun isEmbedding-eq-hasPropFibers embed-f
      prop-g : ∀ a d -> isProp (fiber (g a) d)
      prop-g a = eqFun isEmbedding-eq-hasPropFibers (embed-g a)

      ΣB : {c : C} (d : D c) -> (fiber f c) -> Type (ℓ-max ℓB ℓD)
      ΣB d (a' , a'-path) = Σ[ b ∈ B a' ] (PathP (\i -> D (a'-path i)) (g a' b) d)

      isProp-ΣB : ∀ {c : C} (d : D c) (fib : fiber f c) -> isProp (ΣB d fib)
      isProp-ΣB d (a' , fa'=c) (b1 , p1) (b2 , p2) = \i -> b-path i , p-path i
        where
        gb-path : Path (D (f a')) (g a' b1) (g a' b2)
        gb-path = transP-sym p1 (symP p2)

        gb-square : SquareP (\i j -> D (fa'=c j)) p1 p2 gb-path (reflᵉ d)
        gb-square i j = (transP-sides-filler p1 refl (symP p2)) j i

        b-path : b1 == b2
        b-path = isEqInv (embed-g a' _ _) gb-path

        gb-b-path : (cong (g a')) b-path == gb-path
        gb-b-path = isEqSec (embed-g a' _ _) gb-path

        p-path : PathP (\i -> PathP (\j -> D (fa'=c j)) (g a' (b-path i)) d) p1 p2
        p-path =
          transport (\k -> PathP (\i -> PathP (\j -> D (fa'=c j)) (gb-b-path (~ k) i) d) p1 p2)
            gb-square

      prop-fg : ∀ a -> isProp (fiber fg a)
      prop-fg (c , d) ((a1 , b1) , p1) ((a2 , b2) , p2) =
        (\i -> (fst (a-path i) , fst (Σb-path i)) ,
               (\j -> (snd (a-path i) j , snd (Σb-path i) j)))
        where
        a1-path : f a1 == c
        a1-path = cong fst p1
        a2-path : f a2 == c
        a2-path = cong fst p2

        a-path : Path (fiber f c) (a1 , a1-path) (a2 , a2-path)
        a-path = prop-f c _ _

        Σb1 : ΣB d (a1 , a1-path)
        Σb1 = (b1 , cong snd p1)
        Σb2 : ΣB d (a2 , a2-path)
        Σb2 = (b2 , cong snd p2)

        Σb-path : PathP (\i -> ΣB d (a-path i)) Σb1 Σb2
        Σb-path = isProp->PathP (\i -> isProp-ΣB d (a-path i))


module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : B -> Type ℓC}
         {f : A -> B} {g : (a : A) -> C (f a)}
  where
  private
    fg : A -> Σ B C
    fg a = f a , g a

  opaque
    isEmbedding-Σ-isSet : isEmbedding f -> (∀ b -> isSet (C b)) -> isEmbedding fg
    isEmbedding-Σ-isSet embed-f isSet-C = eqInv isEmbedding-eq-hasPropFibers prop-fg
      where
      prop-f : ∀ b -> isProp (fiber f b)
      prop-f = eqFun isEmbedding-eq-hasPropFibers embed-f

      prop-fg : ∀ a -> isProp (fiber fg a)
      prop-fg (b , c) (a1 , p1) (a2 , p2) =
        \i -> a-path i , (\j -> (b-path i j) , (c-path i j))
        where
        check-p1 : fg a1 == (b , c)
        check-p1 = p1

        ans1 : (a1 , cong fst p1) == (a2 , cong fst p2)
        ans1 = prop-f b _ _

        a-path : a1 == a2
        a-path = cong fst ans1
        b-path : PathP (\i -> f (a-path i) == b) (cong fst p1) (cong fst p2)
        b-path = cong snd ans1

        c-path : PathP (\i -> PathP (\j -> C (b-path i j)) (g (a-path i)) c) (cong snd p1) (cong snd p2)
        c-path = isProp->PathP (\i -> isOfHLevelPathP' 1 (\j -> isSet-C _) _ _)
