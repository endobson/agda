{-# OPTIONS --cubical #-}

module base where

open import Level
open import Agda.Primitive.Cubical public
open import Agda.Builtin.Cubical.Path public

open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )

infix 4 _===_
data _===_ {a} {A : Set a} (x : A) : A -> Set a where
  refl-=== : x === x

{-# BUILTIN EQUALITY _===_  #-}


Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A a b = PathP (λ _ → A) a b

infix 4 _==_
_==_ : {i : Level} -> {A : Set i} → A → A → Set i
_==_ {A = A} = Path A

refl : {i : Level} {A : Set i} {x : A} → Path A x x
refl {x = x} = \ i -> x

data Bot : Set where

bot-elim : {A : Set} -> Bot -> A
bot-elim ()

¬ : {a : Level} -> Set a -> Set a
¬ A = A -> Bot

record Top : Set where
  constructor tt

infixr 1 _⊎_

data _⊎_ (A : Set) (B : Set) : Set where
  inj-l : (a : A) → A ⊎ B
  inj-r : (b : B) → A ⊎ B

data Dec {a : Level} (A : Set a) : Set a where
  yes : A -> Dec A
  no : ¬ A -> Dec A

data exists : {A : Set} -> (B : A -> Set) -> Set (suc zero) where
 existence : {A : Set} -> {B : A -> Set} -> (x : A) -> (y : B x) -> exists B

infixr 4 _,_
infixr 2 _×_

data _×_ {a b : Level} (A : Set a) (B : Set b): Set (a ⊔ b) where
  _,_ : (a : A) -> (b : B) -> A × B

proj₁ : {a b : Level} {A : Set a} -> {B : Set b} -> A × B -> A
proj₁ (a , b) = a

proj₂ : {a b : Level} {A : Set a} -> {B : Set b} -> A × B -> B
proj₂ (a , b) = b


data Boolean : Set where
  true : Boolean
  false : Boolean
