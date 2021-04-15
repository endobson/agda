{-# OPTIONS --cubical --safe --exact-split #-}

module haequiv where

open import base
open import cubical
open import equality
open import equivalence

private
  variable
    ℓ : Level
    A B : Type ℓ

private
  section : (f : A -> B) (g : B -> A) -> Type _
  section f g = ∀ b -> f (g b) == b

  retract : (f : A -> B) (g : B -> A) -> Type _
  retract f g = ∀ a -> g (f a) == a

record isHAEquiv (fun : A -> B) : Type (ℓ-max (levelOf A) (levelOf B)) where
  field
    inv : B -> A
    rightInv : section fun inv
    leftInv : retract fun inv
    comm : (a : A) -> cong fun (leftInv a) == (rightInv (fun a))

  -- Implemented following proof in standard library
  comm' : (b : B) -> cong inv (rightInv b) == (leftInv (inv b))
  comm' b = (\i j -> hcomp (\k -> \{ (i = i0) -> g (rinv b j)
                                   ; (i = i1) -> linv (g b) (j ∨ (~ k))
                                   ; (j = i0) -> linv (g b) (i ∧ (~ k))
                                   ; (j = i1) -> g b
                                   })
                           (cap1 i j))
    where
    f = fun
    g = inv
    rinv = rightInv
    linv = leftInv

    --    fgfg --  f (linv (g)) -- fg
    --     |                        |
    -- fg (rinv)                   rinv
    --     |                        |
    --    fg   --     rinv      --  1

    cap0 : Square (\j -> f (g (rinv b j)))
                  (\j -> rinv b j)
                  (\i -> f (linv (g b) i))
                  (\i -> rinv b i)
    cap0 i j = hcomp (\k -> \{ (i = i0) -> f (g (rinv b j))
                             ; (i = i1) -> rinv b j
                             ; (j = i0) -> comm (g b) (~ k) i
                             ; (j = i1) -> rinv b i
                             })
                     (rinv (rinv b j) i)

    filler : I -> I -> A
    filler i j = hfill (\k -> \{ (j = i0) -> g (rinv b k)
                               ; (j = i1) -> g b
                               })
                       (inS (linv (g b) j)) i

    cap1 : Square (\ j -> g (rinv b j))
                  (\ j -> g b)
                  (\ i -> linv (g b) i)
                  (\ i -> g b)
    cap1 i j = hcomp (\k -> \{ (i = i0) -> linv (g (rinv b j)) k
                             ; (i = i1) -> filler j k
                             ; (j = i0) -> linv (linv (g b) i) k
                             ; (j = i1) -> filler i k
                             })
                     (g (cap0 i j))

equiv->isHAEquiv : (eq : A ≃ B) -> isHAEquiv ⟨ eq ⟩
equiv->isHAEquiv eq .isHAEquiv.inv      = eqInv eq
equiv->isHAEquiv eq .isHAEquiv.rightInv = eqSec eq
equiv->isHAEquiv eq .isHAEquiv.leftInv  = eqRet eq
equiv->isHAEquiv eq .isHAEquiv.comm a   = flip-square (slideSquare (eqComm eq a))
