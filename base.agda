{-# OPTIONS --cubical --safe --exact-split #-}

module base where

open import Agda.Builtin.Sigma public
open import Agda.Builtin.Nat public using (Nat; zero; suc)
open import Level public
  using    ( Level )
  renaming ( zero to ℓ-zero
           ; suc  to ℓ-suc
           ; _⊔_  to ℓ-max
           )

open import cubical

open cubical public using (isContr)

Type : (ℓ : Level) → Set (ℓ-suc ℓ)
Type ℓ = Set ℓ

ℓ-one : Level
ℓ-one = ℓ-suc ℓ-zero

ℓ-two : Level
ℓ-two = ℓ-suc ℓ-one

Type₀ : Type ℓ-one
Type₀ = Type ℓ-zero

Type₁ : Type ℓ-two
Type₁ = Type ℓ-one


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


data Boolean : Type₀ where
  true : Boolean
  false : Boolean

-- Case analysis
case_of_ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} -> A -> (A -> B) -> B
case x of f = f x

case_return_of_ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} -> (a : A) -> (B : A -> Type ℓ₂) -> ((x : A) -> B x) -> B a
case x return B of f = f x


-- Variable argument levels
private
  Nary : {ℓ : Level} -> Nat -> Type ℓ -> Type ℓ -> Type ℓ
  Nary zero    x y = y
  Nary (suc n) x y = x -> (Nary n x y)

  ℓ-max*-acc : (n : Nat) (acc : Level) -> Nary n Level Level
  ℓ-max*-acc zero    ℓ-acc   = ℓ-acc
  ℓ-max*-acc (suc n) ℓ-acc ℓ = ℓ-max*-acc n (ℓ-max ℓ-acc ℓ)

ℓ-max* : (n : Nat) -> Nary n Level Level
ℓ-max* n  = ℓ-max*-acc n ℓ-zero
