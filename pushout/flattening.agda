{-# OPTIONS --cubical --safe --exact-split #-}

module pushout.flattening where

{- Reimplemented following the implementation in Cubical.HITs.Pushout.Flattening. -}

open import base
open import cubical renaming (glue to cglue)
open import equality-path
open import equality.square
open import equivalence
open import functions
open import isomorphism
open import pushout
open import univalence


module _ {ℓA ℓB ℓC ℓP : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> B) (g : A -> C)
         (F : B -> Type ℓP) (G : C -> Type ℓP) (eq : ∀ a -> F (f a) ≃ G (g a))
         where

  private
    P : Pushout f g -> Type ℓP
    P = Pushout-rec F G (\a -> ua (eq a))

    f' : Σ[ a ∈ A ] (F (f a)) -> Σ B F
    f' (a , p) = (f a , p)
    g' : Σ[ a ∈ A ] (F (f a)) -> Σ C G
    g' (a , p) = (g a , eqFun (eq a) p)


  ΣPushout-iso' : Iso (Σ (Pushout f g) P) (Pushout f' g')
  ΣPushout-iso' = iso fwd bkw fb bf
    where
    fwd : (Σ (Pushout f g) P) -> (Pushout f' g')
    fwd (inj-l b , p)  = inj-l (b , p)
    fwd (inj-r c , p)  = inj-r (c , p)
    fwd (glue a i , p) =
      hcomp (\k -> \{ (i = i0) -> glue (a , p) (~ k)
                    ; (i = i1) -> inj-r (g a , p)
                    })
        (inj-r (g a , ua-unglue (eq a) i p))

    bkw : (Pushout f' g') -> (Σ (Pushout f g) P)
    bkw (inj-l (b , p))  = inj-l b , p
    bkw (inj-r (c , p))  = inj-r c , p
    bkw (glue (a , p) i) = glue a i , ua-glue₀ (eq a) i p

    fb : ∀ x -> fwd (bkw x) == x
    fb (inj-l (b , p)) = refl
    fb (inj-r (c , p)) = refl
    fb (glue (a , p) i) j =
      hcomp (\k -> \{ (i = i0) -> glue (a , p) (~ k)
                    ; (i = i1) -> base
                    ; (j = i1) -> glue (a , p) (i ∨ ~ k)
                    })
        base
      where
      base : Pushout f' g'
      base = inj-r (g a , ua-unglue (eq a) i (ua-glue₀ (eq a) i p))

    bf : ∀ x -> bkw (fwd x) == x
    bf ((inj-l b) , p) = refl
    bf ((inj-r c) , p) = refl
    bf x@(glue a i , p) j =
      comp (\_ -> Σ (Pushout f g) P)
        (\k -> \{ (i = i0) -> glue a (~ k) , ua-glue₀ (eq a) (~ k) p
                ; (i = i1) -> base
                ; (j = i1) -> glue a (i ∨ ~ k) , shift p (~ k)
                })
        base
      where
      base : Σ (Pushout f g) P
      base = inj-r (g a) , (ua-unglue (eq a) i p)

      shift : (P (glue a i) -> (k : I) -> P (glue a (i ∨ k)))
      shift p k =
        ua-glue (eq a) (i ∨ k)
          (\{ (i = i0) (k = i0) -> p })
          (inS (ua-unglue (eq a) i p))



module _ {ℓA ℓB ℓC ℓP : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {f : A -> B} {g : A -> C}
         (P : Pushout f g -> Type ℓP)
         where
  private
    F : B -> Type ℓP
    F = P ∘ inj-l
    G : C -> Type ℓP
    G = P ∘ inj-r
    paths : ∀ a -> F (f a) == G (g a)
    paths a i = P (glue a i)
    eq : ∀ a -> F (f a) ≃ G (g a)
    eq a = pathToEquiv (paths a)

    P' : Pushout f g -> Type ℓP
    P' = Pushout-rec F G (\a -> (ua (pathToEquiv (paths a))))

    f' : Σ[ a ∈ A ] (F (f a)) -> Σ B F
    f' (a , p) = (f a , p)
    g' : Σ[ a ∈ A ] (F (f a)) -> Σ C G
    g' (a , p) = (g a , transport (paths a) p)

  ΣPushout-iso : Iso (Σ (Pushout f g) P') (Pushout f' g')
  ΣPushout-iso = ΣPushout-iso' f g F G eq
