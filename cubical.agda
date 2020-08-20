{-# OPTIONS --cubical --safe --exact-split #-}

module cubical where

open import Agda.Builtin.Cubical.Glue public
open import Agda.Builtin.Cubical.Path public

open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1
           )

open import Agda.Builtin.Cubical.Sub public
  renaming ( inc        to inS
           ; primSubOut to outS
           )

open Helpers public
  using ( isContr
        ; fiber
        ; hfill
        ; fill
        )
