{-# OPTIONS --cubical #-}

module equality where

open import Level
open import base

cong : {a b : Level} {A : Set a} {B : Set b} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y  
cong f refl = refl

cong2 : {i1 i2 i3 : Level} -> {A : Set i1} -> {B : Set i2} -> {C : Set i3} -> 
        (f : A -> B -> C) -> {a c : A} -> {b d : B} -> a == c -> b == d -> f a b == f c d
cong2 f refl refl = refl

sym : {a : Level} {A : Set a} -> {x y : A} -> x == y -> y == x 
sym refl = refl

trans : {a : Level} {A : Set a} -> {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

subst : {a p : Level} -> {A : Set a} -> {x y : A} -> (P : A → Set p) -> x == y -> P x -> P y
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

_!=_ : {a : Level} -> {A : Set a} -> A -> A -> Set a
x != y = ¬ (x == y)


infixl 20 _>=>_
_>=>_ : {a : Level} {A : Set a} -> {x y z : A} -> x == y -> y == z -> x == z
refl >=> refl = refl

