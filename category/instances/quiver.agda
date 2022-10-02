{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.set

module category.instances.quiver where

data WalkingQuiverObj : Type ℓ-zero where
  wq-vertices : WalkingQuiverObj
  wq-edges : WalkingQuiverObj

data WalkingQuiverMor : WalkingQuiverObj -> WalkingQuiverObj -> Type ℓ-zero where
  wq-id : (p : WalkingQuiverObj) -> WalkingQuiverMor p p
  wq-source : WalkingQuiverMor wq-edges wq-vertices
  wq-target : WalkingQuiverMor wq-edges wq-vertices

WalkingQuiverCat : PreCategory ℓ-zero ℓ-zero
WalkingQuiverCat = record
  { Obj = WalkingQuiverObj
  ; Mor = WalkingQuiverMor
  ; id = wq-id _
  ; _⋆_ = wq-compose
  ; ⋆-left-id = wq-left-id
  ; ⋆-right-id = wq-right-id
  ; ⋆-assoc = wq-assoc
  }
  where

  wq-compose : {a b c : WalkingQuiverObj} -> 
               WalkingQuiverMor a b -> WalkingQuiverMor b c -> WalkingQuiverMor a c
  wq-compose (wq-id _) f = f
  wq-compose wq-source (wq-id _) = wq-source
  wq-compose wq-target (wq-id _) = wq-target

  wq-left-id : {s t : WalkingQuiverObj} -> (f : WalkingQuiverMor s t) -> wq-compose (wq-id _) f == f
  wq-left-id _ = refl

  wq-right-id : {s t : WalkingQuiverObj} -> (f : WalkingQuiverMor s t) -> wq-compose f (wq-id _) == f
  wq-right-id (wq-id _) = refl
  wq-right-id wq-source = refl
  wq-right-id wq-target = refl

  wq-assoc : {s t u v : WalkingQuiverObj} -> 
             (f : WalkingQuiverMor s t) -> 
             (g : WalkingQuiverMor t u) -> 
             (h : WalkingQuiverMor u v) -> 
             wq-compose (wq-compose f g) h == wq-compose f (wq-compose g h)
  wq-assoc (wq-id _) _         _ = refl
  wq-assoc wq-source (wq-id _) _ = refl
  wq-assoc wq-target (wq-id _) _ = refl

Quiv : {ℓo ℓm : Level} -> (C : PreCategory ℓo ℓm) -> Type (ℓ-max ℓo ℓm)
Quiv C = Functor WalkingQuiverCat C

Quiver : (ℓ : Level) -> Type (ℓ-suc ℓ)
Quiver ℓ = Quiv (SetC ℓ)

