{-# OPTIONS --cubical --safe --exact-split #-}

module base where

open import Agda.Builtin.Cubical.Glue public
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Sigma public

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

open import Level public
  using    ( Level )
  renaming ( zero to ℓ-zero
           ; suc  to ℓ-suc
           ; _⊔_  to ℓ-max
           ; Setω  to Typeω
           )

Type : (ℓ : Level) → Set (ℓ-suc ℓ)
Type ℓ = Set ℓ

Type₀ : Type (ℓ-suc ℓ-zero)
Type₀ = Type ℓ-zero

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

record Lift {ℓA} ℓ (A : Type ℓA) : Type (ℓ-max ℓA ℓ) where
  constructor lift
  field
    lower : A


infix 4 _===_
data _===_ {A : Type ℓ} (x : A) : A -> Type ℓ where
  refl-=== : x === x

Path : (A : Type ℓ) -> A -> A -> Type ℓ
Path A a b = PathP (λ _ → A) a b

infix 4 _==_
_==_ : A -> A -> Type _
_==_ {A = A} = Path A

refl : {x : A} → Path A x x
refl {x = x} = \ i -> x

levelOf : {ℓ : Level} -> Type ℓ -> Level
levelOf {ℓ} _ = ℓ

-- Common datatypes

data Bot : Type₀ where

bot-elim : Bot -> A
bot-elim ()

¬ : Type ℓ -> Type ℓ
¬ A = A -> Bot

record Top : Type₀ where
  constructor tt

infixr 1 _⊎_

data _⊎_ (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  inj-l : (a : A) → A ⊎ B
  inj-r : (b : B) → A ⊎ B

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : (A : Type ℓ₁) (B : A → Type ℓ₂) → Type (ℓ-max ℓ₁ ℓ₂)
Σ-syntax = Σ

syntax Σ-syntax A (\x -> B) = Σ[ x ∈ A ] B

-- Altrnative spelling of fst. For use with structured data.
⟨_⟩ : {ℓ₁ ℓ₂ : Level} -> {A : Type ℓ₁} -> {B : A -> Type ℓ₂} -> Σ A B -> A
⟨ (a , _) ⟩ = a

infixr 2 _×_

_×_ : (A : Type ℓ₁) (B : Type ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
A × B = Σ A (\_ -> B)

proj₁ : A × B -> A
proj₁ (a , b) = a

proj₂ : A × B -> B
proj₂ (a , b) = b


data Nat : Type₀ where
 zero : Nat
 suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Boolean : Type₀ where
  true : Boolean
  false : Boolean
