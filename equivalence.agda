{-# OPTIONS --cubical --safe --exact-split #-}

module equivalence where

open import base
open import cubical
open import equality-path
open import equality.square
open import functions
open import hlevel.base
open import isomorphism
open import sigma.base

open import Agda.Builtin.Cubical.Glue
  using ()
  renaming ( pathToEquiv    to lineToEquiv
           )

open import equivalence.base public

private
  variable
    ℓ : Level
    A1 A2 : Type ℓ
    A B C : Type ℓ

module _ {f : A1 -> A2} (eq-f : isEquiv f) where
  isEqComm : (a : A1) -> Square (isEqSec eq-f (f a)) refl (cong f (isEqRet eq-f a)) refl
  isEqComm a i = eq-f .equiv-proof (f a) .snd (a , refl) i .snd

module _ (e : A1 ≃ A2) where
  eqComm : (a : A1) -> Square (eqSec e (eqFun e a)) refl (cong (eqFun e) (eqRet e a)) refl
  eqComm = isEqComm (snd e)

  eqCtr : (a : A2) -> fiber (eqFun e) a
  eqCtr a = e .snd .equiv-proof a .fst

  eqCtrPath : (a : A2) -> (f : fiber (eqFun e) a) -> (eqCtr a) == f
  eqCtrPath a = e .snd .equiv-proof a .snd

equiv-path : {eq₁ eq₂ : A1 ≃ A2} -> eqFun eq₁ == eqFun eq₂ -> eq₁ == eq₂
equiv-path p = ΣProp-path isProp-isEquiv p

pathToEquiv : A1 == A2 -> A1 ≃ A2
pathToEquiv p = lineToEquiv (\i -> p i)


liftEquiv : {ℓA : Level} (ℓ : Level) (A : Type ℓA) -> Lift ℓ A ≃ A
liftEquiv ℓ A .fst = Lift.lower
liftEquiv ℓ A .snd .equiv-proof a = (lift a , refl) , contr a
  where
  contr : (a : A) -> (a2 : fiber Lift.lower a) -> (lift a , refl) == a2
  contr a (_ , p2) i = (lift (p2 (~ i)) , (\j -> p2 (~ i ∨ j)))

∘-equiv : B ≃ C -> A ≃ B -> A ≃ C
∘-equiv f g = isoToEquiv (equivToIso f ∘ⁱ equivToIso g)

equiv⁻¹ : A ≃ B -> B ≃ A
equiv⁻¹ f = isoToEquiv (iso⁻¹ (equivToIso f))

infixl 20 _>eq>_
_>eq>_ : A ≃ B -> B ≃ C -> A ≃ C
_>eq>_ f g = ∘-equiv g f


rightInverse-isEquiv : (f : A -> B) (g : B -> A) -> f ∘ g == idfun B -> isEquiv f -> isEquiv g
rightInverse-isEquiv f g id isEq = isoToIsEquiv (iso g f inv (\b i -> id i b))
  where
  inv : ∀ a -> g (f a) == a
  inv a = sym (isEqRet isEq (g (f a))) >=>
          (\i -> isEqInv isEq (id i (f a))) >=>
          isEqRet isEq a

leftInverse-isEquiv : (f : A -> B) (g : B -> A) -> f ∘ g == idfun B -> isEquiv g -> isEquiv f
leftInverse-isEquiv f g id isEq = isoToIsEquiv (iso f g (\a i -> id i a) inv)
  where
  inv : ∀ a -> g (f a) == a
  inv a = (\i -> g (f (isEqSec isEq a (~ i)))) >=>
          (\i -> g (id i (isEqInv isEq a))) >=>
          (isEqSec isEq a)
