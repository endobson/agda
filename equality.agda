module equality where

open import Level using (Level; _⊔_; suc)

REL : {i j : Level} -> (Set i) -> (Set j) -> (l : Level) -> Set (i ⊔ j ⊔ (suc l))
REL A B l = A -> B -> Set l


infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x

{-# BUILTIN EQUALITY _==_  #-}

cong : {a b : Level} {A : Set a} {B : Set b} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y  
cong f refl = refl

cong2 : {A B C : Set} -> (f : A -> B -> C) -> {a c : A} -> {b d : B} -> a == c -> b == d -> f a b == f c d
cong2 f refl refl = refl


sym : {A : Set} -> {x y : A} -> x == y -> y == x 
sym refl = refl

trans : {a : Level} {A : Set a} -> {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

-- substp : {A : Set} -> {x y : A} -> (P : A → Set) -> x == y -> P x -> P y
-- substp P refl px = px

subst : {A : Set} -> {x y : A} -> (P : A → Set) -> x == y -> P x -> P y
subst P refl px = px

infix  1 begin_
infixr 2 _==<>_ _==<_>_
infix  3 _end

begin_ : {a : Level} -> {A : Set a} -> {x y : A} -> x == y -> x == y
begin x==y  =  x==y
 
_==<>_ : {a : Level} {A : Set a} -> (x : A) {y : A} -> x == y -> x == y
x ==<> x==y  =  x==y
 
_==<_>_ : {a : Level} {A : Set a} (x : A) {y z : A} -> x == y -> y == z -> x == z
x ==< x==y > y==z  =  trans x==y y==z

_end : {a : Level} {A : Set a} (x : A) -> x == x
x end  =  refl

record Top : Set where
  constructor tt

data Bot : Set where

bot-elim : {A : Set} -> Bot -> A
bot-elim ()

¬ : Set -> Set
¬ A = A -> Bot

_!=_ : {A : Set} -> A -> A -> Set
x != y = ¬ (x == y)


infixl 20 _>=>_
_>=>_ : {A : Set} -> {x y z : A} -> x == y -> y == z -> x == z
refl >=> refl = refl

infixr 1 _⊎_

data _⊎_ (A : Set) (B : Set) : Set where
  inj-l : (a : A) → A ⊎ B
  inj-r : (b : B) → A ⊎ B

data Dec (A : Set) : Set where
  yes : A -> Dec A
  no : ¬ A -> Dec A

data exists : {A : Set} -> (B : A -> Set) -> Set where
 existence : {A : Set} -> {B : A -> Set} -> (x : A) -> (y : B x) -> exists B

infixr 4 _,_
infixr 2 _×_

data _×_ (A : Set) (B : Set): Set where
  _,_ : (a : A) -> (b : B) -> A × B

proj₁ : {A : Set} -> {B : Set} -> A × B -> A
proj₁ (a , b) = a

proj₂ : {A : Set} -> {B : Set} -> A × B -> B
proj₂ (a , b) = b
