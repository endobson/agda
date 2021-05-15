{-# OPTIONS --cubical --safe --exact-split #-}

module funext where

open import base
open import cubical
open import univalence

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> B a -> Type ℓ

module _ {f g : (a : A) -> B a} where

  funExt : ((x : A) -> f x == g x) -> f == g
  funExt p i x = p x i
  funExt⁻ : f == g -> ((x : A) -> f x == g x)
  funExt⁻ eq a i = eq i a

  private
    fib : (p : f == g) -> fiber funExt p
    fib p = ((\x i -> (p i) x) , refl)
    funExt-fiber-isContr : (p : f == g) -> (fi : fiber funExt p) -> fib p == fi
    funExt-fiber-isContr p (h , eq) i = (funExt⁻ (eq (~ i)) , \j -> eq (~ i ∨ j))

    isEquiv-funExt : isEquiv funExt
    equiv-proof isEquiv-funExt p = (fib p , funExt-fiber-isContr p)

  funExtEquiv : ((x : A) -> f x == g x) ≃ (f == g)
  funExtEquiv = (funExt , isEquiv-funExt)

  funExtPath : ((x : A) -> f x == g x) == (f == g)
  funExtPath = ua funExtEquiv

funExt2 : {f g : (a : A) -> (b : B a) -> C a b} -> ((a : A) -> (b : B a) -> f a b == g a b) -> f == g
funExt2 p i a b = p a b i
