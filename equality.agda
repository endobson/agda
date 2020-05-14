module equality where

infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x

{-# BUILTIN EQUALITY _==_  #-}

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y 
cong f refl = refl

sym : {A : Set} -> {x y : A} -> x == y -> y == x 
sym refl = refl

trans : {A : Set} -> {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

-- substp : {A : Set} -> {x y : A} -> (P : A → Set) -> x == y -> P x -> P y
-- substp P refl px = px

subst : {A : Set} -> {x y : A} -> (P : A → Set) -> x == y -> P x -> P y
subst P refl px = px

infix  1 begin_
infixr 2 _==<>_ _==<_>_
infix  3 _end

begin_ : {A : Set} -> {x y : A} -> x == y -> x == y
begin x==y  =  x==y
 
_==<>_ : {A : Set} -> (x : A) {y : A} -> x == y -> x == y
x ==<> x==y  =  x==y
 
_==<_>_ : {A : Set} (x : A) {y z : A} -> x == y -> y == z -> x == z
x ==< x==y > y==z  = trans x==y y==z

_end : {A : Set} (x : A) -> x == x
x end  =  refl

data Top : Set where
  tt : Top

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
