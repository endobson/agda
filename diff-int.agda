{-# OPTIONS --cubical --safe --exact-split #-}

module diff-int where

open import base
open import nat
open import set-quotient

private
  record DiffInt' : Type₀ where
    field
      a : Nat
      b : Nat

  _~_ : DiffInt' -> DiffInt' -> Type₀
  _~_ x y = (x.a +' y.b) == (y.a +' x.b)
    where
    module x = DiffInt' x
    module y = DiffInt' y

  paths->path : {x y : DiffInt'} -> (DiffInt'.a x == DiffInt'.a y) -> (DiffInt'.b x == DiffInt'.b y) ->
                x == y
  paths->path {x} {y} pa pb i = record { a = pa i ; b = pb i }

DiffInt : Type₀
DiffInt = DiffInt' / _~_

_d+'_ : DiffInt' -> DiffInt' -> DiffInt'
x d+' y = record
  { a = x.a +' y.a
  ; b = x.b +' y.b
  }
  where
  module x = DiffInt' x
  module y = DiffInt' y


d+'-commute : {x y : DiffInt'} -> (x d+' y) == (y d+' x)
d+'-commute {x} {y} = paths->path pa pb
  where
  module x = DiffInt' x
  module y = DiffInt' y
  pa : x.a +' y.a == y.a +' x.a
  pa = +'-commute {x.a} {y.a}
  pb : x.b +' y.b == y.b +' x.b
  pb = +'-commute {x.b} {y.b}
