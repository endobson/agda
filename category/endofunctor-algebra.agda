{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.functor

module category.endofunctor-algebra where

private
  variable
    ℓObj ℓMor : Level

EndoFunctor : (C : PreCategory ℓObj ℓMor) -> Type (ℓ-max ℓObj ℓMor)
EndoFunctor C = Functor C C


record Algebra (C : PreCategory ℓObj ℓMor) (F : EndoFunctor C) : Type (ℓ-max ℓObj ℓMor) where
  module C = PreCategory C
  module F = Functor F
  field
    carrier : C.Obj
    value : C [ F.obj carrier , carrier ]
