{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.renamings2 where

open import base
open import cubical
open import relation
open import functions

private
  variable
    ℓ : Level
    A : Type ℓ

record RenamingT (Atom : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    R : Type ℓ
    apply-renaming : R ↪ (Atom ≃ Atom)



isFixedPoint : (A -> A) -> A -> Type _
isFixedPoint f a = (f a == a)

FixedPoints : (A -> A) -> Type _
FixedPoints {A = A} f = Σ A (isFixedPoint f)

hasDecidableFixedPoints : (A -> A) -> Type _
hasDecidableFixedPoints f = ∀ a -> Dec (isFixedPoint f a)


module _ {A : Type ℓ} (RT : RenamingT A) where
  private
    module RT = RenamingT RT
    R = RT.R
    apply-renaming = RT.apply-renaming

--  isFiniteRenaming : Pred R _
--  isFiniteRenaming 
  
  
-- isFiniteRenaming : -> Type _
-- isFiniteRenaming RT = 
--   ∀ (r : RT.R) -> apply-renaming r
--   where


record isRenamingT (Atom : Type ℓ) (R : Type ℓ) : Type ℓ where
  field
    apply-renaming : R -> Atom -> Atom

    
