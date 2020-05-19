{-# OPTIONS --cubical #-}

module equality where

open import Level
open import base

cong : {a b : Level} {A : Set a} {B : Set b} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y  
cong f p i = f (p i)

cong2 : {i1 i2 i3 : Level} -> {A : Set i1} -> {B : Set i2} -> {C : Set i3} -> 
        (f : A -> B -> C) -> {a c : A} -> {b d : B} -> a == c -> b == d -> f a b == f c d
cong2 f p1 p2 i = f (p1 i) (p2 i)

sym : {a : Level} {A : Set a} -> {x y : A} -> x == y -> y == x 
sym p i = p (~ i)

transport : ∀ {i} {A B : Set i} -> A == B -> A -> B
transport p a = transp (\ i -> p i) i0 a

_∙∙_∙∙_ : ∀ {a} {A : Set a} {w x y z : A} -> w == x -> x == y -> y == z -> w == z
(p ∙∙ q ∙∙ r) i =
  hcomp (\ j -> \ { (i = i0) -> p (~ j)
                  ; (i = i1) -> r j})
        (q i)

trans : {a : Level} {A : Set a} -> {x y z : A} -> x == y -> y == z -> x == z
trans p1 p2 = refl ∙∙ p1 ∙∙ p2


subst : {a p : Level} -> {A : Set a} -> {x y : A} -> (P : A → Set p) -> x == y -> P x -> P y
subst P path = transport (\ i -> (P (path i)))

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
p1 >=> p2 = trans p1 p2

