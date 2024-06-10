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

∘-isEquiv : {f : A -> B} {g : B -> C} -> isEquiv g -> isEquiv f -> isEquiv (g ∘ f)
∘-isEquiv {A = A} {B = B} {C = C} {f = f} {g = g} eg ef .equiv-proof c = center , isCtr
  where
  pg : isContr (fiber g c)
  pg = isEquiv.equiv-proof eg c
  cg : fiber g c
  cg = fst pg
  b : B
  b = (fst cg)
  pf : isContr (fiber f b)
  pf = isEquiv.equiv-proof ef b
  cf : fiber f b
  cf = fst pf
  a : A
  a = (fst cf)
  center : fiber (g ∘ f) c
  center = (a , cong g (snd cf) >=> snd cg)
  opaque
    isCtr : (fib : fiber (g ∘ f) c) -> center == fib
    isCtr (a' , gfa'=c) = \i -> fst-path i , snd-path i
      where
      p2g : cg == (f a' , gfa'=c)
      p2g = snd pg (f a' , gfa'=c)

      p2f : cf == (a' , (sym (cong fst p2g)))
      p2f = snd pf (a' , (sym (cong fst p2g)))

      p1 : g b == c
      p1 = snd cg

      p2 : f a == b
      p2 = snd cf

      p3 : g (f a) == c
      p3 = snd center

      p4 : g (f a') == c
      p4 = gfa'=c

      p5 : f a' == b
      p5 = sym (cong fst p2g)

      p6 : a == a'
      p6 = (cong fst p2f)

      fst-path : (fst cf) == a'
      fst-path = p6

      snd-path : Square p3 p4 (cong (g ∘ f) p6) (reflᵉ c)
      snd-path = square-corner-append s4 s1
        where
        s1 : Square p1 p4 (sym (cong g p5)) (reflᵉ c)
        s1 = (cong snd p2g)

        s2 : Square (cong g p5) (cong g p2) (sym (cong (g ∘ f) p6)) (reflᵉ (g b))
        s2 i j = g (cong snd p2f (~ i) j)

        s3 : Square (reflᵉ (g b)) p3 (sym (cong g p2)) p1
        s3 = doubleCompPath-filler (cong g p2) refl p1

        s4 : Square p3 (cong g p5) (cong (g ∘ f) p6) (sym p1)
        s4 = symP (square-corner-append s2 s3)

∘-equiv : B ≃ C -> A ≃ B -> A ≃ C
∘-equiv (g , eg) (f , ef) = g ∘ f , ∘-isEquiv eg ef

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
