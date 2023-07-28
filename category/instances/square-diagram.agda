{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

open import base
open import hlevel
open import equality-path
open import category.base
open import relation
open import fin-algebra
open import cubical
open import equivalence
open import univalence
open import isomorphism
open import fin

module category.instances.square-diagram where

data SquareDiagramObj : Type ℓ-zero where
  sq-upper-left : SquareDiagramObj
  sq-upper-right : SquareDiagramObj
  sq-lower-left : SquareDiagramObj
  sq-lower-right : SquareDiagramObj

data SquareDiagramMor : SquareDiagramObj -> SquareDiagramObj -> Type ℓ-zero where
  sq-id : (p : SquareDiagramObj) -> SquareDiagramMor p p
  sq-left : SquareDiagramMor sq-upper-left sq-lower-left
  sq-right : SquareDiagramMor sq-upper-right sq-lower-right
  sq-top : SquareDiagramMor sq-upper-left sq-upper-right
  sq-bottom : SquareDiagramMor sq-lower-left sq-lower-right
  sq-diagonal : SquareDiagramMor sq-upper-left sq-lower-right

private
  Discrete-SquareDiagramObj : Discrete SquareDiagramObj
  Discrete-SquareDiagramObj = 
    subst Discrete (sym (ua fin-eq >=> FinT=Fin 4)) discreteFin
    where
    fin-eq : SquareDiagramObj ≃ FinT 4
    fin-eq = isoToEquiv (iso f g fg gf)
      where
      f : SquareDiagramObj -> FinT 4
      f sq-upper-left  = inj-l tt
      f sq-upper-right = inj-r (inj-l tt)
      f sq-lower-left  = inj-r (inj-r (inj-l tt))
      f sq-lower-right = inj-r (inj-r (inj-r (inj-l tt)))

      g : FinT 4 -> SquareDiagramObj
      g (inj-l tt)                         = sq-upper-left
      g (inj-r (inj-l tt))                 = sq-upper-right
      g (inj-r (inj-r (inj-l tt)))         = sq-lower-left
      g (inj-r (inj-r (inj-r (inj-l tt)))) = sq-lower-right

      fg : ∀ x -> f (g x) == x
      fg (inj-l tt)                         = refl
      fg (inj-r (inj-l tt))                 = refl
      fg (inj-r (inj-r (inj-l tt)))         = refl
      fg (inj-r (inj-r (inj-r (inj-l tt)))) = refl
      
      gf : ∀ x -> g (f x) == x
      gf sq-upper-left  = refl
      gf sq-upper-right = refl
      gf sq-lower-left  = refl
      gf sq-lower-right = refl


  Discrete-SquareDiagramMor : {x y : SquareDiagramObj} -> Discrete (SquareDiagramMor x y)
  Discrete-SquareDiagramMor (sq-id sq-upper-left)   (sq-id sq-upper-left)  = yes refl
  Discrete-SquareDiagramMor (sq-id sq-upper-right)  (sq-id sq-upper-right) = yes refl
  Discrete-SquareDiagramMor (sq-id sq-lower-left)   (sq-id sq-lower-left)  = yes refl
  Discrete-SquareDiagramMor (sq-id sq-lower-right)  (sq-id sq-lower-right) = yes refl
  Discrete-SquareDiagramMor sq-left     sq-left     = yes refl
  Discrete-SquareDiagramMor sq-right    sq-right    = yes refl
  Discrete-SquareDiagramMor sq-top      sq-top      = yes refl
  Discrete-SquareDiagramMor sq-bottom   sq-bottom   = yes refl
  Discrete-SquareDiagramMor sq-diagonal sq-diagonal = yes refl

  isSet-SquareDiagramObj : isSet SquareDiagramObj
  isSet-SquareDiagramObj = Discrete->isSet Discrete-SquareDiagramObj

  isSet-SquareDiagramMor : {x y : SquareDiagramObj} -> isSet (SquareDiagramMor x y)
  isSet-SquareDiagramMor = Discrete->isSet Discrete-SquareDiagramMor


SquareDiagramCat : PreCategory ℓ-zero ℓ-zero
SquareDiagramCat = record
  { Obj = SquareDiagramObj
  ; Mor = SquareDiagramMor
  ; id = sq-id _
  ; _⋆_ = sq-compose
  ; ⋆-left-id = sq-left-id
  ; ⋆-right-id = sq-right-id
  ; ⋆-assoc = sq-assoc
  ; isSet-Mor = isSet-SquareDiagramMor
  }
  where

  sq-compose : {a b c : SquareDiagramObj} -> 
               SquareDiagramMor a b -> SquareDiagramMor b c -> SquareDiagramMor a c
  sq-compose (sq-id p)   g         = g
  sq-compose sq-left     (sq-id _) = sq-left
  sq-compose sq-right    (sq-id _) = sq-right
  sq-compose sq-top      (sq-id _) = sq-top
  sq-compose sq-bottom   (sq-id _) = sq-bottom
  sq-compose sq-diagonal (sq-id _) = sq-diagonal
  sq-compose sq-top      sq-right  = sq-diagonal
  sq-compose sq-left     sq-bottom = sq-diagonal

  sq-left-id : {s t : SquareDiagramObj} -> (f : SquareDiagramMor s t) -> sq-compose (sq-id _) f == f
  sq-left-id _ = refl

  sq-right-id : {s t : SquareDiagramObj} -> (f : SquareDiagramMor s t) -> sq-compose f (sq-id _) == f
  sq-right-id (sq-id _)   = refl
  sq-right-id sq-left     = refl
  sq-right-id sq-right    = refl
  sq-right-id sq-top      = refl
  sq-right-id sq-bottom   = refl
  sq-right-id sq-diagonal = refl

  sq-assoc : {s t u v : SquareDiagramObj} -> 
             (f : SquareDiagramMor s t) -> 
             (g : SquareDiagramMor t u) -> 
             (h : SquareDiagramMor u v) -> 
             sq-compose (sq-compose f g) h == sq-compose f (sq-compose g h)
  sq-assoc (sq-id _) _ _ = refl
  sq-assoc sq-left (sq-id _) _ = refl
  sq-assoc sq-right (sq-id _) _ = refl
  sq-assoc sq-top (sq-id _) _ = refl
  sq-assoc sq-bottom (sq-id _) _ = refl
  sq-assoc sq-diagonal (sq-id _) _ = refl
  sq-assoc sq-left sq-bottom (sq-id _) = refl
  sq-assoc sq-top sq-right (sq-id _) = refl
