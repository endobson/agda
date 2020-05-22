{-# OPTIONS --cubical --safe --exact-split #-}

module relation where

open import Level
open import base


private
  variable
    i j a b c : Level
    A : Set a
    B : Set b
    C : Set c

REL : {i j : Level} -> (Set i) -> (Set j) -> (l : Level) -> Set _
REL A B l = A -> B -> Set l

Rel : (Set i) -> (l : Level) -> Set (i ⊔ (suc l))
Rel A l = REL A A l


Reflexive : {A : Set a} -> Rel A i -> Set _
Reflexive _~_ = ∀ {a} -> a ~ a

Irreflexive : {A : Set a} -> Rel A i -> Set _
Irreflexive _~_ = ∀ {a} -> ¬(a ~ a)

Symmetric : {A : Set a} -> Rel A i -> Set _ 
Symmetric _~_ = ∀ {a b} -> (a ~ b) -> (b ~ a)

Asymmetric : {A : Set a} -> Rel A i -> Set _ 
Asymmetric _~_ = ∀ {a b} -> (a ~ b) -> ¬ (b ~ a)

Antisymmetric : {A : Set a} -> Rel A i -> Set _ 
Antisymmetric _~_ = ∀ {a b} -> (a ~ b) -> (b ~ a) -> a == b

Transitive : {A : Set a} -> Rel A i -> Set _
Transitive _~_ = ∀ {a b c} -> (a ~ b) -> (b ~ c) -> (a ~ c)

_⇒_ : REL A B i -> REL A B j -> Set _
P ⇒ Q = ∀ x y -> P x y -> Q x y

private
  _on_ : (B -> B -> C) -> (A -> B) -> A -> A -> C
  _*_ on f = (\ a b -> (f a) * (f b))

_=[_]⇒_ : Rel A i -> (A -> B)-> Rel B j -> Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)

_Preserves_⇢_ : (A -> B) -> Rel A i -> Rel B j -> Set _
f Preserves P ⇢ Q = P =[ f ]⇒ Q
