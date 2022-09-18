{-# OPTIONS --cubical --safe --exact-split #-}

module cubical where


open import Agda.Builtin.Cubical.Glue public
  renaming ( prim^glue      to glue
           ; pathToEquiv    to lineToEquiv
           )
open import Agda.Builtin.Cubical.Path public

open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
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
        ; fiber -- (f : (A -> B)) -> Σ[ x ∈ A ] (f x == y)
        ; hfill
        ; fill
        )

open import Agda.Builtin.Sigma
open import Level

private
  Type : (ℓ : Level) → Set (suc ℓ)
  Type ℓ = Set ℓ

Glue : ∀ {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) {φ : I}
       → (Te : Partial φ (Σ (Type ℓ₂) (\T -> T ≃ A)))
       → Type ℓ₂
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

unglue : {ℓ ℓ' : Level} {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o -> T o ≃ A)} -> primGlue A T e → A
unglue φ = prim^unglue {φ = φ}
