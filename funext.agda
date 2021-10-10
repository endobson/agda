{-# OPTIONS --cubical --safe --exact-split #-}

module funext where

open import base
open import equality
open import functions
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

module _ {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A -> Type ℓb} {C : Type ℓc}
         (a1 a2 : A)
         {f1 : (B a1) -> C}
         {f2 : (B a2) -> C}
         {p : (B a1) == (B a2)}
         (same : (b1 : (B a1)) (b2 : (B a2)) -> (f1 b1) == (f2 b2))
         where
  private
    f-path-t : PathP (\k -> (p k) -> C)
                     (\x -> f1 (transport refl x))
                     (\x -> f2 (transport refl x))
    f-path-t k x = same x1 x2 k
      where
      x1 : B a1
      x1 = transport (\j -> p (~ j ∧ k)) x
      x2 : B a2
      x2 = transport (\j -> p (j ∨ k)) x

    f-path-left : f1 ∘ (transport refl) == f1
    f-path-left = funExt (\x -> cong f1 (transportRefl x))

    f-path-right : f2 ∘ (transport refl) == f2
    f-path-right = funExt (\x -> cong f2 (transportRefl x))

  abstract
    funExtDep : PathP (\k -> (p k) -> C) f1 f2
    funExtDep = transP-left (transP-right (sym f-path-left) f-path-t) f-path-right
