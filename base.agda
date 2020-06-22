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

infix 4 _===_
data _===_ {a} {A : Set a} (x : A) : A -> Set a where
  refl-=== : x === x

Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A a b = PathP (λ _ → A) a b

infix 4 _==_
_==_ : {i : Level} -> {A : Set i} → A → A → Set i
_==_ {A = A} = Path A

refl : {i : Level} {A : Set i} {x : A} → Path A x x
refl {x = x} = \ i -> x

Type : (ℓ : Level) → Set (ℓ-suc ℓ)
Type ℓ = Set ℓ

Type₀ : Type (ℓ-suc ℓ-zero)
Type₀ = Type ℓ-zero

levelOf : {ℓ : Level} -> Type ℓ -> Level
levelOf {ℓ} _ = ℓ

-- Common datatypes

data Bot : Set where

bot-elim : {ℓ : Level} {A : Type ℓ} -> Bot -> A
bot-elim ()

¬ : {a : Level} -> Set a -> Set a
¬ A = A -> Bot

record Top : Set where
  constructor tt

infixr 1 _⊎_

data _⊎_ (A : Set) (B : Set) : Set where
  inj-l : (a : A) → A ⊎ B
  inj-r : (b : B) → A ⊎ B

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) → Type (ℓ-max ℓ₁ ℓ₂)
Σ-syntax = Σ

syntax Σ-syntax A (\x -> B) = Σ[ x ∈ A ] B

infixr 4 _,_
infixr 2 _×_

data _×_ {ℓ₁ ℓ₂ : Level} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  _,_ : (a : A) -> (b : B) -> A × B

proj₁ : {a b : Level} {A : Set a} -> {B : Set b} -> A × B -> A
proj₁ (a , b) = a

proj₂ : {a b : Level} {A : Set a} -> {B : Set b} -> A × B -> B
proj₂ (a , b) = b


data Nat : Type₀ where
 zero : Nat
 suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Boolean : Set where
  true : Boolean
  false : Boolean
