{-# OPTIONS --cubical --safe --exact-split #-}

module equivalence where

open import base
open import cubical

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A A1 A2 : Type ℓ
    B : A -> Type ℓ


idfun : (A : Type ℓ) → A → A
idfun _ x = x

idIsEquiv : (A : Type ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , \ z i -> z .snd (~ i) , \ j -> z .snd (~ i ∨ j))

idEquiv : (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

Glue : ∀ (A : Type ℓ₁) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ₂ ] T ≃ A))
       → Type ℓ₂
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

ua : ∀ {A B : Type ℓ} -> A ≃ B -> A == B
ua {A = A} {B = B} e i = Glue B (\ { (i = i0) -> (A , e)
                                   ; (i = i1) -> (B , idEquiv B) })

module _ {f : A1 -> A2} (eq-f : isEquiv f) where
  isEqFun : A1 -> A2
  isEqFun = f

  isEqInv : A2 -> A1
  isEqInv a = eq-f .equiv-proof a .fst .fst

  isEqSec : (a : A2) -> isEqFun (isEqInv a) == a
  isEqSec a = eq-f .equiv-proof a .fst .snd

  isEqRet : (a : A1) -> isEqInv (isEqFun a) == a
  isEqRet a i = eq-f .equiv-proof (f a) .snd (a , refl) i .fst

module _ (e : A1 ≃ A2) where
  eqFun : A1 -> A2
  eqFun = fst e

  eqInv : A2 -> A1
  eqInv = isEqInv (snd e)

  eqSec : (a : A2) -> eqFun (eqInv a) == a
  eqSec = isEqSec (snd e)

  eqRet : (a : A1) -> eqInv (eqFun a) == a
  eqRet = isEqRet (snd e)

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


  funExt-isEquiv : isEquiv funExt
  equiv-proof funExt-isEquiv p = (fib p , funExt-fiber-isContr p)

  funExtEquiv : ((x : A) -> f x == g x) ≃ (f == g)
  funExtEquiv = (funExt , funExt-isEquiv)

  funExtPath : ((x : A) -> f x == g x) == (f == g)
  funExtPath = ua funExtEquiv
